/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.AlgebraicInduction.CaseIII.Relabel.ForkedArm
import CombinatorialRigidity.Mathlib.Basic.Countable.Defs

/-!
# Case III: the case `d = 3`, the case of a chain and `lem:case-III`

Case III of KT Theorem 5.5 (Katoh and Tanigawa 2011, *A proof of the molecular conjecture*, Discrete
Comput. Geom. **45**, §6.4), presented in `sec:molecular-algebraic-induction-caseIII`. The file
proves:

* the bound of KT eq. (6.22) off the zeros of a polynomial
  (`exists_nested_rankPolynomial_lower_all_k`, `lem:case-III-nested-rank-lower`);
* the case `d = 3`, KT Lemma 6.10 (`case_III_candidate_dispatch`,
  `lem:case-III-candidate-dispatch-d3`), which no main result uses;
* for a chain `v₀v₁⋯v_d` of length `d`, the form `r` and the choice of a panel (KT
  eqs. (6.65)–(6.67); `chainData_fire_discriminator`, `lem:case-III-chain-discriminator`), and Case
  III for the chain (`chainData_dispatch`, `lem:case-III-chain-dispatch`), from the proof of KT
  Lemma 6.13;
* `lem:case-III`, KT Lemma 6.13 (`case_III_realization_all_k`), which the induction of KT
  Theorem 5.5 uses (`theorem_55_minimalKDof_k_all_k`, `AlgebraicInduction/Theorem55.lean`).

The lemmas before them compare the rows of two endpoint selectors and give the polynomials that make
three, or `k + 1`, normals linearly independent. `CaseIII/Arms.lean` builds the framework `(G, p_1)`
and rotates the panel of `v`, and `CaseIII/Relabel/` renames the bodies.
-/

namespace CombinatorialRigidity.Molecular

variable {k : ℕ}

open scoped Graph

variable {α β : Type*}
variable {K : Type*} [Field K]

/-! ## Two endpoint selectors with the same rows

Steps of `lem:case-III-candidate-dispatch-d3` and `lem:case-III-chain-dispatch`: the frameworks
`ofNormals G ends q` and `ofNormals G ends' q` have the same rows when `ends` and `ends'` agree on
the links of `G`, or give each link its ends in some order. The proofs change the selector at the
edges at the vertex put back, which are not links of `G − v`. -/

/-- **Selectors that agree on the links give the same rows** (a step of
`lem:case-III-candidate-dispatch-d3` and `lem:case-III-chain-dispatch`): if `ends` and `ends'` agree
on every link of `G` (`hagree`), then `ofNormals G ends q` and `ofNormals G ends' q` have the same
set of rigidity rows. `case_III_candidate_dispatch` and the dispatch of a chain use it for a
selector changed at the two edges at the vertex put back.

Both sets quantify over the links `G.IsLink e u v` and read `ends` only through the hinge
`panelSupportExtensor (q ((ends e).1, ·)) (q ((ends e).2, ·))` (`toBodyHinge_supportExtensor`,
`ofNormals_ends`, `ofNormals_normal`); the row `hingeRow u v r` does not depend on `ends`. So at
each link the hinges, hence the hinge-row blocks `(span C)^⊥`, of the two frameworks coincide, and
the row sets are equal. The proof rewrites by these evaluation lemmas, not by `whnf` (TACTICS-QUIRKS
§38). -/
theorem PanelHingeFramework.rigidityRows_ofNormals_congr_ends
    {G : Graph α β} {ends ends' : β → α × α} (q : α × Fin (k + 2) → K)
    (hagree : ∀ e u v, G.IsLink e u v → ends e = ends' e) :
    (PanelHingeFramework.ofNormals G ends q).toBodyHinge.rigidityRows
      = (PanelHingeFramework.ofNormals G ends' q).toBodyHinge.rigidityRows := by
  -- On any link `e u v`, the support extensors coincide (`ends e = ends' e`), so the hinge-row
  -- blocks coincide; the generator `hingeRow u v r` is `ends`-free. Each membership re-provides
  -- the same `⟨e, u, v, hlink, r, …⟩` witness.
  have hsupp : ∀ e u v, G.IsLink e u v →
      (PanelHingeFramework.ofNormals G ends q).toBodyHinge.supportExtensor e =
        (PanelHingeFramework.ofNormals G ends' q).toBodyHinge.supportExtensor e := by
    intro e u v hlink
    simp only [PanelHingeFramework.toBodyHinge_supportExtensor,
      PanelHingeFramework.ofNormals_ends, PanelHingeFramework.ofNormals_normal,
      hagree e u v hlink]
  have hblock : ∀ e u v, G.IsLink e u v →
      (PanelHingeFramework.ofNormals G ends q).toBodyHinge.hingeRowBlock e =
        (PanelHingeFramework.ofNormals G ends' q).toBodyHinge.hingeRowBlock e := by
    intro e u v hlink
    simp only [BodyHingeFramework.hingeRowBlock, hsupp e u v hlink]
  apply Set.eq_of_subset_of_subset
  · rintro φ ⟨e, u, v, hlink, r, hr, rfl⟩
    refine ⟨e, u, v, hlink, r, ?_, rfl⟩
    rwa [← hblock e u v hlink]
  · rintro φ ⟨e, u, v, hlink, r, hr, rfl⟩
    refine ⟨e, u, v, hlink, r, ?_, rfl⟩
    rwa [hblock e u v hlink]

/-- **Selectors that give each link its ends give the same rows** (a step of
`lem:case-III-chain-dispatch`): if `ends` and `ends'` each give every link `e` of `G` from `u` to
`v` the ends `(u, v)` or `(v, u)` (`hagree`), then `ofNormals G ends q` and `ofNormals G ends' q`
have the same set of rigidity rows. `chainData_interior_realization_hρGv` uses it to pass from the
selector `Graph.ChainData.candidateEnds i ends₀`, at which `chainData_bottom_relabel`
(`lem:case-III-chain-relabel-rows`) gives the bottom rows, to the selector of the `i`-th framework.

The hinge at `e` is `panelSupportExtensor (q (ends e).1) (q (ends e).2)`, and exchanging the two
normals negates it (`panelSupportExtensor_swap`). So at each link the hinges of the two frameworks
span the same line `span {panelSupportExtensor (q u) (q v)}`, the hinge-row blocks `(span {·})^⊥`
coincide, and the row sets are equal. -/
theorem PanelHingeFramework.rigidityRows_ofNormals_congr_ends_swap
    {G : Graph α β} {ends ends' : β → α × α} (q : α × Fin (k + 2) → K)
    (hagree : ∀ e u v, G.IsLink e u v →
      (ends e = (u, v) ∨ ends e = (v, u)) ∧ (ends' e = (u, v) ∨ ends' e = (v, u))) :
    (PanelHingeFramework.ofNormals G ends q).toBodyHinge.rigidityRows
      = (PanelHingeFramework.ofNormals G ends' q).toBodyHinge.rigidityRows := by
  -- On any link `e u v`, the support extensor of either framework is `±panelSupportExtensor (q u)
  -- (q v)` (each `ends`/`ends'` recording branch collapses through `panelSupportExtensor_swap`), so
  -- both single-element spans equal `span {panelSupportExtensor (q u) (q v)}`.
  have hspan : ∀ (sel : β → α × α), (∀ e u v, G.IsLink e u v →
        sel e = (u, v) ∨ sel e = (v, u)) → ∀ e u v, G.IsLink e u v →
      Submodule.span K {(PanelHingeFramework.ofNormals G sel q).toBodyHinge.supportExtensor e}
        = Submodule.span K {panelSupportExtensor (fun i => q (u, i)) (fun i => q (v, i))} := by
    intro sel hsel e u v hlink
    simp only [PanelHingeFramework.toBodyHinge_supportExtensor, PanelHingeFramework.ofNormals_ends,
      PanelHingeFramework.ofNormals_normal]
    rcases hsel e u v hlink with he | he
    · rw [he]
    · rw [he]
      -- the recorded singleton is `panelSupportExtensor (q v) (q u) = -panelSupportExtensor (q u)
      -- (q v)`; a `-1` unit collapses the sign.
      refine Submodule.span_singleton_eq_span_singleton.mpr ⟨-1, ?_⟩
      rw [Units.smul_def, Units.val_neg, Units.val_one, neg_one_smul, panelSupportExtensor_swap,
        neg_neg]
  -- Hence the two frameworks' hinge-row blocks (the dual annihilators of those spans) coincide on
  -- every link of `G`.
  have hblock : ∀ e u v, G.IsLink e u v →
      (PanelHingeFramework.ofNormals G ends q).toBodyHinge.hingeRowBlock e =
        (PanelHingeFramework.ofNormals G ends' q).toBodyHinge.hingeRowBlock e := by
    intro e u v hlink
    simp only [BodyHingeFramework.hingeRowBlock,
      hspan ends (fun e u v h => (hagree e u v h).1) e u v hlink,
      hspan ends' (fun e u v h => (hagree e u v h).2) e u v hlink]
  apply Set.eq_of_subset_of_subset
  · rintro φ ⟨e, u, v, hlink, r, hr, rfl⟩
    refine ⟨e, u, v, hlink, r, ?_, rfl⟩
    rwa [← hblock e u v hlink]
  · rintro φ ⟨e, u, v, hlink, r, hr, rfl⟩
    refine ⟨e, u, v, hlink, r, ?_, rfl⟩
    rwa [hblock e u v hlink]

/-! ## Normals linearly independent off the zeros of a determinant

Steps of `lem:case-I-realization-h65`, `lem:case-III-candidate-dispatch-d3` and
`lem:case-III-chain-discriminator`, whose proofs choose the normals off the zeros of a product of
nonzero polynomials, fixed before the choice, as explained after `lem:case-I-realization`. -/

/-- **Three normals linearly independent off the zeros of a polynomial** (a step of
`lem:case-I-realization-h65` and `lem:case-III-candidate-dispatch-d3`): for `1 ≤ k` and distinct
`a`, `b` and `c`, there is a nonzero polynomial `P` in the normals such that `q(a, ·)`, `q(b, ·)`
and `q(c, ·)` are linearly independent wherever `P(q) ≠ 0`, over any field `K`.

The proof. `P` is the determinant of the generic `3 × 3` matrix, renamed along the injective
`f (i, j) = (![a, b, c] i, Fin.castLE h3 j)`; it is nonzero by `Matrix.det_mvPolynomialX_ne_zero`
and `MvPolynomial.rename_injective`. At `q`, `P(q)` is the determinant of the first three columns of
the three normals (`MvPolynomial.eval_rename`, `Matrix.mvPolynomialX_mapMatrix_eval`,
`RingHom.map_det`), so these columns are linearly independent
(`Matrix.linearIndependent_rows_of_det_ne_zero`), and so are the normals
(`LinearIndependent.of_comp`). -/
lemma exists_tripleLI_polynomial
    {k : ℕ} {α : Type*} (hk : 1 ≤ k)
    {a b c : α} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ P : MvPolynomial (α × Fin (k + 2)) K, P ≠ 0 ∧
      ∀ q : α × Fin (k + 2) → K, MvPolynomial.eval q P ≠ 0 →
        LinearIndependent K (![fun i => q (a, i), fun i => q (b, i), fun i => q (c, i)] :
          Fin 3 → Fin (k + 2) → K) := by
  classical
  have h3 : (3 : ℕ) ≤ k + 2 := by omega
  have hbinj : Function.Injective (![a, b, c] : Fin 3 → α) := by
    intro i j heq
    fin_cases i <;> fin_cases j <;>
      simp_all [Matrix.cons_val_zero, Matrix.cons_val_one, hab.symm, hac.symm, hbc.symm]
  set f : Fin 3 × Fin 3 → α × Fin (k + 2) :=
    fun p => (![a, b, c] p.1, Fin.castLE h3 p.2) with hf_def
  have hfinj : Function.Injective f := by
    intro ⟨i, j⟩ ⟨i', j'⟩ heq
    simp only [hf_def, Prod.mk.injEq] at heq
    exact Prod.ext (hbinj heq.1) (Fin.castLE_injective h3 heq.2)
  refine ⟨MvPolynomial.rename f (Matrix.mvPolynomialX (Fin 3) (Fin 3) K).det, ?_, ?_⟩
  · -- Nonzero: the generic determinant is nonzero, and `rename f` is injective.
    have hP_ne : (Matrix.mvPolynomialX (Fin 3) (Fin 3) K).det ≠ 0 :=
      Matrix.det_mvPolynomialX_ne_zero (Fin 3) K
    have hren := (MvPolynomial.rename_injective f hfinj).ne hP_ne
    rwa [map_zero] at hren
  · intro q hne
    -- `eval q P = eval (q ∘ f) (det (mvPolynomialX …))` (`MvPolynomial.eval_rename`).
    have hchain : MvPolynomial.eval q (MvPolynomial.rename f
          (Matrix.mvPolynomialX (Fin 3) (Fin 3) K).det) =
        MvPolynomial.eval (fun p : Fin 3 × Fin 3 => (q ∘ f) p)
          (Matrix.mvPolynomialX (Fin 3) (Fin 3) K).det := by
      rw [MvPolynomial.eval_rename]
    -- The literal row family equals the selector family; project to the first three columns.
    have hrows : (![fun i => q (a, i), fun i => q (b, i), fun i => q (c, i)] :
          Fin 3 → Fin (k + 2) → K) =
        fun (i : Fin 3) (j : Fin (k + 2)) => q (![a, b, c] i, j) := by
      ext i j; fin_cases i <;> rfl
    rw [hrows]
    apply LinearIndependent.of_comp
      (LinearMap.pi (fun j : Fin 3 =>
        (LinearMap.proj (Fin.castLE h3 j) : (Fin (k + 2) → K) →ₗ[K] K)))
    have hcomp_eq : (LinearMap.pi
          (fun j : Fin 3 =>
            (LinearMap.proj (Fin.castLE h3 j) : (Fin (k + 2) → K) →ₗ[K] K))) ∘
        (fun (i : Fin 3) (j : Fin (k + 2)) => q (![a, b, c] i, j)) =
        fun (i : Fin 3) (j : Fin 3) => q (![a, b, c] i, Fin.castLE h3 j) := rfl
    rw [hcomp_eq]
    apply Matrix.linearIndependent_rows_of_det_ne_zero
    -- `det B = eval (q ∘ f) (det (mvPolynomialX …)) = eval q P ≠ 0`.
    have hφB : (MvPolynomial.eval (fun p : Fin 3 × Fin 3 => (q ∘ f) p)).mapMatrix
        (Matrix.mvPolynomialX (Fin 3) (Fin 3) K) =
        (fun i j => q (![a, b, c] i, Fin.castLE h3 j)) := by
      have := Matrix.mvPolynomialX_mapMatrix_eval
        (Matrix.of (fun i j : Fin 3 => q (![a, b, c] i, Fin.castLE h3 j)))
      exact this
    have hBdet : Matrix.det (fun i j => q (![a, b, c] i, Fin.castLE h3 j)) =
        MvPolynomial.eval (fun p : Fin 3 × Fin 3 => (q ∘ f) p)
          (Matrix.mvPolynomialX (Fin 3) (Fin 3) K).det := by
      rw [← hφB, RingHom.map_det]
    rw [hBdet, ← hchain]
    exact hne

/-- **`k + 1` normals linearly independent off the zeros of a polynomial** (a step of
`lem:case-III-chain-discriminator`): for an injective `cand : Fin (k + 1) → α`, there is a nonzero
polynomial `P` in the normals such that the normals `q(cand i, ·)` are linearly independent wherever
`P(q) ≠ 0`, over any field `K`. It is the fourth factor in the proof of
`lem:case-III-chain-discriminator`, a `d × d` minor of the matrix with the rows
`q(u_0), …, q(u_{d−1})` (`exists_shared_redundancy_and_matched_candidate`, with `d = k + 1`).

The proof is that of `exists_tripleLI_polynomial`, with the generic `(k + 1) × (k + 1)` determinant
and `f (i, j) = (cand i, Fin.castSucc j)`. -/
lemma exists_tupleLI_polynomial
    {k : ℕ} {α : Type*} {cand : Fin (k + 1) → α} (hcand : Function.Injective cand) :
    ∃ P : MvPolynomial (α × Fin (k + 2)) K, P ≠ 0 ∧
      ∀ q : α × Fin (k + 2) → K, MvPolynomial.eval q P ≠ 0 →
        LinearIndependent K (fun (i : Fin (k + 1)) (j : Fin (k + 2)) => q (cand i, j)) := by
  classical
  set f : Fin (k + 1) × Fin (k + 1) → α × Fin (k + 2) :=
    fun p => (cand p.1, Fin.castSucc p.2) with hf_def
  have hfinj : Function.Injective f := by
    intro ⟨i, j⟩ ⟨i', j'⟩ heq
    simp only [hf_def, Prod.mk.injEq] at heq
    exact Prod.ext (hcand heq.1) (Fin.castSucc_injective _ heq.2)
  refine ⟨MvPolynomial.rename f (Matrix.mvPolynomialX (Fin (k + 1)) (Fin (k + 1)) K).det, ?_, ?_⟩
  · have hP_ne : (Matrix.mvPolynomialX (Fin (k + 1)) (Fin (k + 1)) K).det ≠ 0 :=
      Matrix.det_mvPolynomialX_ne_zero (Fin (k + 1)) K
    have hren := (MvPolynomial.rename_injective f hfinj).ne hP_ne
    rwa [map_zero] at hren
  · intro q hne
    have hchain : MvPolynomial.eval q (MvPolynomial.rename f
          (Matrix.mvPolynomialX (Fin (k + 1)) (Fin (k + 1)) K).det) =
        MvPolynomial.eval (fun p : Fin (k + 1) × Fin (k + 1) => (q ∘ f) p)
          (Matrix.mvPolynomialX (Fin (k + 1)) (Fin (k + 1)) K).det := by
      rw [MvPolynomial.eval_rename]
    apply LinearIndependent.of_comp
      (LinearMap.pi (fun j : Fin (k + 1) =>
        (LinearMap.proj (Fin.castSucc j) : (Fin (k + 2) → K) →ₗ[K] K)))
    have hcomp_eq : (LinearMap.pi
          (fun j : Fin (k + 1) =>
            (LinearMap.proj (Fin.castSucc j) : (Fin (k + 2) → K) →ₗ[K] K))) ∘
        (fun (i : Fin (k + 1)) (j : Fin (k + 2)) => q (cand i, j)) =
        fun (i : Fin (k + 1)) (j : Fin (k + 1)) => q (cand i, Fin.castSucc j) := rfl
    rw [hcomp_eq]
    apply Matrix.linearIndependent_rows_of_det_ne_zero
    have hφB : (MvPolynomial.eval (fun p : Fin (k + 1) × Fin (k + 1) => (q ∘ f) p)).mapMatrix
        (Matrix.mvPolynomialX (Fin (k + 1)) (Fin (k + 1)) K) =
        (fun i j => q (cand i, Fin.castSucc j)) := by
      have := Matrix.mvPolynomialX_mapMatrix_eval
        (Matrix.of (fun i j : Fin (k + 1) => q (cand i, Fin.castSucc j)))
      exact this
    have hBdet : Matrix.det (fun i j => q (cand i, Fin.castSucc j)) =
        MvPolynomial.eval (fun p : Fin (k + 1) × Fin (k + 1) => (q ∘ f) p)
          (Matrix.mvPolynomialX (Fin (k + 1)) (Fin (k + 1)) K).det := by
      rw [← hφB, RingHom.map_det]
    rw [hBdet, ← hchain]
    exact hne

/-! ## The case `d = 3` (`lem:case-III-candidate-dispatch-d3`) -/

/-- **The case `d = 3` of Case III** (`lem:case-III-candidate-dispatch-d3`; KT Lemma 6.10, p. 680):
let `K` be infinite and `D = bodyBarDim n = screwDim 2 = 6` (`hn`), and let `G` be simple with
distinct vertices `v`, `a`, `b` and `c`, such that the edges of `G` at `v` are `e_a : va` and
`e_b : vb` (`hclv`), and those at `a` are `e_a` and `e_c : ac` (`hcla`), and let `e₀ ∉ E(G)` label
the new edge `ab` of `Gab = G.splitOff v a b e₀`. Suppose that `G` and `Gab` have deficiency `0`,
that `Gab` has a generic full-rank realization (`hsplitGP`), and that for every endpoint selector
that gives each link of `Gab` its ends in some order there is a nonzero polynomial `P` in the
normals with `rank R(G − v, q) ≥ D(|V(Gab)| − 1) − (D − 2)` wherever `P(q) ≠ 0` (`h622lb`, as
`lem:case-III-nested-rank-lower` gives it). Then `G` has a generic full-rank realization. No main
result uses it: the proof of `lem:case-III` takes the case of a chain, whose case `d = 3` it is.

The proof, as in the proof of `lem:case-III-candidate-dispatch-d3` (KT pp. 682–691). Let `Q` be the
realization of `Gab`; its selector `Q.ends` gives each link of `Gab` its ends in some order. Four
nonzero polynomials are fixed before the normals: that of `exists_rankPolynomial_of_IH_linking` for
`Q`, that of `h622lb` at `Q.ends`, that of `exists_generalPosition_polynomial`, and that of
`exists_tripleLI_polynomial` for `a`, `b` and `c`; `MvPolynomial.exists_eval_ne_zero₄` gives normals
`q` off their zeros. At `q`, `ofNormals Gab Q.ends q` is in general position, and its rank, at least
`D(|V(Gab)| − 1)` by the first factor and at most that by `lem:relative-deficiency-rank-bound`
(`finrank_span_rigidityRows_add_deficiency_le`), makes it infinitesimally rigid on `V(Gab)` (KT
eq. (6.18)). `exists_candidateRow_bottomRows_of_rigidOn` gives the form `r` (here `ρ`), with the
bound of the second factor (KT eq. (6.22)), and the bottom rows `w`, which the proof states at the
orientation `(a, b)`, with `−ρ` if `Q.ends e₀ = (b, a)`. As `q(a)`, `q(b)` and `q(c)` are linearly
independent, by the fourth factor, `exists_homogeneousIncidence_of_normals` and
`exists_complementIso_ne_zero_of_homogeneousIncidence` (the proof of KT Claim 6.12, p. 690) give
`u : Fin 3` and a normal `n'`, linearly independent of the `u`-th of the three, on whose hinge with
it `ρ` does not vanish. For `u = 0`, `case_III_arm_realization` gives the realization, with the
selector `ends₁`, `Q.ends` with `e_a ↦ (v, a)` and `e_b ↦ (v, b)`, whose rows on `G − v` are those
of `Q.ends` (`rigidityRows_ofNormals_congr_ends`); for `u = 1`, `case_III_arm_realization_M2`; and
for `u = 2`, `case_III_arm_realization_M3`, at `G − a` with the selector `ends₃`, `Q.ends` with
`e_c ↦ (a, c)`, `e_a ↦ (a, v)` and `e_b ↦ (v, b)`. -/
theorem PanelHingeFramework.case_III_candidate_dispatch [Infinite K]
    [Finite α] [Finite β]
    (G : Graph α β) (v a b c : α) (e_a e_b e_c e₀ : β)
    (hsimple : G.Simple)
    (hav : a ≠ v) (hbv : b ≠ v) (hba : b ≠ a) (hcv : c ≠ v) (hca : c ≠ a) (hbc : b ≠ c)
    (heab : e_a ≠ e_b) (heac : e_a ≠ e_c)
    (hlea : G.IsLink e_a v a) (hleb : G.IsLink e_b v b) (hlec : G.IsLink e_c a c)
    (hclv : ∀ e x, G.IsLink e v x → e = e_a ∨ e = e_b)
    (hcla : ∀ e x, G.IsLink e a x → e = e_a ∨ e = e_c)
    (he₀ : e₀ ∉ E(G))
    -- The bound of KT eq. (6.22) at `G − v` off the zeros of a polynomial, for every selector that
    -- gives each link of `Gab` its ends, as `exists_nested_rankPolynomial_lower_all_k` gives it.
    (h622lb : ∀ (ends : β → α × α),
      (∀ e u w, (G.splitOff v a b e₀).IsLink e u w → ends e = (u, w) ∨ ends e = (w, u)) →
      ∃ P : MvPolynomial (α × Fin 4) K, P ≠ 0 ∧
        ∀ q : α × Fin 4 → K, MvPolynomial.eval q P ≠ 0 →
          screwDim 2 * (V(G.splitOff v a b e₀).ncard - 1) - (screwDim 2 - 2)
            ≤ Module.finrank K (Submodule.span K
                (PanelHingeFramework.ofNormals (G.removeVertex v) ends
                  q).toBodyHinge.rigidityRows))
    {n : ℕ} (hn : Graph.bodyBarDim n = screwDim 2)
    (hdef_Gab : (G.splitOff v a b e₀).deficiency n = 0)
    (hdef : G.deficiency n = 0)
    (hsplitGP : PanelHingeFramework.HasGenericFullRankRealization K 2 n (G.splitOff v a b e₀)) :
    PanelHingeFramework.HasGenericFullRankRealization K 2 n G := by
  classical
  have : Fintype α := Fintype.ofFinite α
  have hGloop : G.Loopless := hsimple.toLoopless
  have hvG : v ∈ V(G) := hlea.left_mem
  have haG : a ∈ V(G) := hlea.right_mem
  have hbG : b ∈ V(G) := hleb.right_mem
  have hcG : c ∈ V(G) := hlec.right_mem
  set Gab := G.splitOff v a b e₀ with hGab
  set Gv := G.removeVertex v with hGv
  have : Gv.Loopless := hGloop.mono (hGv ▸ Graph.removeVertex_le G v)
  -- `Gab` is loopless: a surviving `G`-edge inherits `G`'s looplessness, the fresh `e₀` joins the
  -- distinct `a ≠ b`.
  have hGabloop : Gab.Loopless := by
    rw [Graph.loopless_iff_forall_ne_of_adj]
    rintro x y ⟨e, hlink⟩
    rw [hGab, Graph.splitOff_isLink] at hlink
    rcases hlink with ⟨_, hGlink, _, _⟩ | ⟨_, _, _, _, _, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩
    · exact hGlink.ne
    · exact hba.symm
    · exact hba
  -- 1. The selector `Q.ends` of the realization of `Gab`, which gives each link its ends in some
  -- order. The four polynomials are fixed before the normals `q`, a non-root of their product.
  obtain ⟨Q, _, _, _, hQrec⟩ := id hsplitGP
  have hrec' : ∀ e u w, Gab.IsLink e u w → Q.ends e = (u, w) ∨ Q.ends e = (w, u) := by
    intro e u w he
    rcases hQrec e u w he with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl (Prod.ext h1 h2)
    · exact Or.inr (Prod.ext h1 h2)
  have hends_Gab : ∀ e u w, Gab.IsLink e u w → Gab.IsLink e (Q.ends e).1 (Q.ends e).2 := by
    intro e u w he
    rcases hrec' e u w he with h | h <;> rw [h]
    · exact he
    · exact he.symm
  have hne' : V(Gab).Nonempty := ⟨a, by rw [hGab, Graph.vertexSet_splitOff]; exact ⟨haG, by
    simp [hav]⟩⟩
  have h1_Gab : 1 ≤ V(Gab).ncard := (Set.ncard_pos (Set.toFinite _)).2 hne'
  -- Factor 1 (`P_ab`): the rank polynomial of `Gab` at `Q.ends`, for KT eq. (6.18).
  obtain ⟨N, hNeq, P_ab, hP_abne, hP_abtrans⟩ :=
    PanelHingeFramework.exists_rankPolynomial_of_IH_linking Gab Q.ends hsplitGP hGabloop hends_Gab
  -- Factor 2 (`P_v`): the polynomial of KT eq. (6.22) for `Gv` at `Q.ends`, from `h622lb`.
  obtain ⟨P_v, hP_vne, hP_vtrans⟩ := h622lb Q.ends hrec'
  -- Factor 3 (`Q_gp`): the general-position polynomial for `Gab` at `Q.ends`.
  obtain ⟨Qgp, hQgp_mc, hQgp_pos⟩ := exists_generalPosition_polynomial (K := K) (k := 2) Gab Q.ends
  have hQgp_ne : Qgp ≠ 0 := by
    obtain ⟨f, hf⟩ := Countable.exists_injective_of_infinite α K
    exact fun h => hQgp_mc f hf (by rw [h, map_zero])
  -- Factor 4 (`P_tri`): the determinant that makes `na`, `nb` and `nc` linearly independent.
  obtain ⟨Ptri, hPtri_ne, hPtri_trans⟩ :=
    exists_tripleLI_polynomial (K := K) (k := 2) (by norm_num) hba.symm hca.symm hbc
  -- Normals `q` off the zeros of the four factors.
  obtain ⟨q, hq_ab, hq_v, hq_gp, hq_tri⟩ :=
    MvPolynomial.exists_eval_ne_zero₄ hP_abne hP_vne hQgp_ne hPtri_ne
  -- General position of `ofNormals Gab Q.ends q` (from `Q_gp`).
  have hgp' : (PanelHingeFramework.ofNormals Gab Q.ends q).IsGeneralPosition := hQgp_pos q hq_gp
  -- Infinitesimal rigidity of `ofNormals Gab Q.ends q` (KT eq. (6.18)): `P_ab` gives `N ≤ rank`,
  -- and the deficiency bound (`lem:relative-deficiency-rank-bound`) at `def = 0` the reverse.
  have hFgraph : (PanelHingeFramework.ofNormals Gab Q.ends q).toBodyHinge.graph = Gab := by
    rw [PanelHingeFramework.toBodyHinge_graph, PanelHingeFramework.ofNormals_graph]
  have hFC : ∀ e u w, (PanelHingeFramework.ofNormals Gab Q.ends q).toBodyHinge.graph.IsLink e u w →
      (PanelHingeFramework.ofNormals Gab Q.ends q).toBodyHinge.supportExtensor e ≠ 0 := by
    intro e u w hlink
    rw [hFgraph] at hlink
    refine PanelHingeFramework.supportExtensor_ne_zero_of_isGeneralPosition _ hgp' ?_
    rw [PanelHingeFramework.ofNormals_ends]
    exact (hends_Gab e u w hlink).ne
  have hB2 := BodyHingeFramework.finrank_span_rigidityRows_add_deficiency_le
    (PanelHingeFramework.ofNormals Gab Q.ends q).toBodyHinge hn (by rw [hFgraph]; exact hne') hFC
  rw [hFgraph, hdef_Gab, sub_zero] at hB2
  rw [hdef_Gab, sub_zero] at hNeq
  have hNle := hP_abtrans q hq_ab
  have hrig' : (PanelHingeFramework.ofNormals Gab Q.ends q).toBodyHinge.IsInfinitesimallyRigidOn
      V(Gab) := by
    have hiff := BodyHingeFramework.isInfinitesimallyRigidOn_vertexSet_iff_finrank_span_rigidityRows
      (PanelHingeFramework.ofNormals Gab Q.ends q).toBodyHinge (by rw [hFgraph]; exact hne')
    rw [hFgraph] at hiff
    rw [hiff]
    have hfin_le : Module.finrank K (Submodule.span K
        (PanelHingeFramework.ofNormals Gab Q.ends q).toBodyHinge.rigidityRows) ≤ N := by
      have : (Module.finrank K (Submodule.span K
          (PanelHingeFramework.ofNormals Gab Q.ends q).toBodyHinge.rigidityRows) : ℤ) ≤ N := by
        rw [hNeq]; exact hB2
      exact_mod_cast this
    rw [le_antisymm hfin_le hNle]
    zify [h1_Gab]; linarith [hNeq]
  -- 2. Facts on `Gab` and `Gv`.
  have he₀ab : Gab.IsLink e₀ a b := by
    rw [hGab, Graph.splitOff_isLink]
    exact Or.inr ⟨rfl, hav, hbv, haG, hbG, Or.inl ⟨rfl, rfl⟩⟩
  have hle : ∀ e u w, Gv.IsLink e u w → Gab.IsLink e u w := by
    intro e u w hlink
    rw [hGv, Graph.removeVertex_isLink] at hlink
    obtain ⟨hGlink, hunev, hwnev⟩ := hlink
    have hee₀ : e ≠ e₀ := fun h => he₀ (h ▸ hGlink.edge_mem)
    rw [hGab, Graph.splitOff_isLink]
    exact Or.inl ⟨hee₀, hGlink, hunev, hwnev⟩
  have hsplit : ∀ e u w, Gab.IsLink e u w → Gv.IsLink e u w ∨ e = e₀ := by
    intro e u w hlink
    rw [hGab, Graph.splitOff_isLink] at hlink
    rcases hlink with ⟨hee₀, hGlink, hunev, hwnev⟩ | ⟨he, _⟩
    · exact Or.inl (by rw [hGv, Graph.removeVertex_isLink]; exact ⟨hGlink, hunev, hwnev⟩)
    · exact Or.inr he
  have hvVc : v ∉ V(Gv) := by rw [hGv, Graph.vertexSet_removeVertex]; exact fun h => h.2 rfl
  have hleG : ∀ e u w, Gv.IsLink e u w → G.IsLink e u w := by
    intro e u w hlink; rw [hGv, Graph.removeVertex_isLink] at hlink; exact hlink.1
  -- The links of `Gv` are not `e_a` or `e_b`, which meet `v ∉ V(Gv)`.
  have hGv_off : ∀ {e u w}, Gv.IsLink e u w → e ≠ e_a ∧ e ≠ e_b := fun hlink =>
    ⟨hlea.ne_of_notMem hvVc hleG hlink, hleb.ne_of_notMem hvVc hleG hlink⟩
  have hV4 : 4 ≤ V(G).ncard := by
    have h1 : ({v, a, b, c} : Set α) ⊆ V(G) := by
      intro x hx; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> assumption
    have h2 : ({v, a, b, c} : Set α).ncard = 4 := by
      rw [Set.ncard_insert_of_notMem (by simp [hav.symm, hbv.symm, hcv.symm]),
        Set.ncard_insert_of_notMem (by simp [hba.symm, hca.symm]),
        Set.ncard_insert_of_notMem (by simp [hbc]), Set.ncard_singleton]
    calc 4 = ({v, a, b, c} : Set α).ncard := h2.symm
      _ ≤ V(G).ncard := Set.ncard_le_ncard h1 (Set.toFinite _)
  have hcard : V(Gab).ncard = V(Gv).ncard := by
    simp only [hGab, hGv, Graph.vertexSet_splitOff, Graph.vertexSet_removeVertex]
  have hgp_seed : ∀ x y : α, x ≠ y →
      LinearIndependent K ![fun i => q (x, i), fun i => q (y, i)] := by
    intro x y hxy
    have := hgp' x y hxy
    rw [PanelHingeFramework.ofNormals_normal, PanelHingeFramework.ofNormals_normal] at this
    exact this
  -- 3. The form `ρ` and the bottom rows `w` (`exists_candidateRow_bottomRows_of_rigidOn`).
  have hD : (2 : ℕ) ≤ screwDim 2 := by decide
  have huv : (Q.ends e₀).1 ≠ (Q.ends e₀).2 := by
    rcases hrec' e₀ a b he₀ab with he | he <;> rw [he]
    · exact hba.symm
    · exact hba
  have hne₀ : (PanelHingeFramework.ofNormals Gab Q.ends q).toBodyHinge.supportExtensor e₀ ≠ 0 := by
    apply PanelHingeFramework.supportExtensor_ne_zero_of_isGeneralPosition _ hgp'
    rw [PanelHingeFramework.ofNormals_ends]; exact huv
  have he₀' : Gab.IsLink e₀ (Q.ends e₀).1 (Q.ends e₀).2 := by
    rcases hrec' e₀ a b he₀ab with he | he <;> rw [he]
    · exact he₀ab
    · exact he₀ab.symm
  obtain ⟨ρ, w, _lamAB, _rab, hρne, hρe₀', hρGv', hw, hwmem', _hrab_blk, _hρ_lam, _hedgeGv⟩ :=
    BodyHingeFramework.exists_candidateRow_bottomRows_of_rigidOn (Gab := Gab) (Gv := Gv)
      (ends := Q.ends) (q := q) (e₀ := e₀) hD huv hne₀ he₀' hle hsplit hne' hrig'
      (hP_vtrans q hq_v)
  -- 4. The form and the rows at the orientation `(a, b)`, with `-ρ` if `Q.ends e₀ = (b, a)`.
  set na := (fun i => q (a, i)) with hna
  set nb := (fun i => q (b, i)) with hnb
  set nc := (fun i => q (c, i)) with hnc
  -- The hinge of `e₀` as a `panelSupportExtensor`.
  have hsupp_e₀ : ∀ (r : Module.Dual K (ScrewSpace K 2)),
      r ((PanelHingeFramework.ofNormals Gab Q.ends q).toBodyHinge.supportExtensor e₀) =
        r (panelSupportExtensor (fun i => q ((Q.ends e₀).1, i))
          (fun i => q ((Q.ends e₀).2, i))) := by
    intro r
    rw [PanelHingeFramework.toBodyHinge_supportExtensor, PanelHingeFramework.ofNormals_ends,
      PanelHingeFramework.ofNormals_normal, PanelHingeFramework.ofNormals_normal]
  obtain ⟨ρ0, hρ0ne, hρ0e₀, hρ0Gv, hw0mem⟩ :
      ∃ ρ0 : Module.Dual K (ScrewSpace K 2), ρ0 ≠ 0 ∧
        ρ0 (panelSupportExtensor na nb) = 0 ∧
        BodyHingeFramework.hingeRow a b ρ0 ∈ Submodule.span K
          (PanelHingeFramework.ofNormals Gv Q.ends q).toBodyHinge.rigidityRows ∧
        (∀ j, w j ∈ (PanelHingeFramework.ofNormals Gv Q.ends q).toBodyHinge.rigidityRows ∨
          ∃ ρ' : Module.Dual K (ScrewSpace K 2),
            ρ' (panelSupportExtensor na nb) = 0 ∧ w j = BodyHingeFramework.hingeRow a b ρ') := by
    rcases hrec' e₀ a b he₀ab with he | he
    · -- recorded `(a, b)`: take `ρ0 := ρ`.
      refine ⟨ρ, hρne, ?_, ?_, ?_⟩
      · rw [hsupp_e₀, he] at hρe₀'; exact hρe₀'
      · rw [he] at hρGv'; exact hρGv'
      · intro j
        rcases hwmem' j with hgen | ⟨ρ', hρ'e₀, hwj⟩
        · exact Or.inl hgen
        · refine Or.inr ⟨ρ', ?_, by rw [hwj, he]⟩
          rw [hsupp_e₀, he] at hρ'e₀; exact hρ'e₀
    · -- recorded `(b, a)`: take `ρ0 := -ρ` (`hingeRow b a (-ρ) = hingeRow a b ρ`).
      refine ⟨-ρ, neg_ne_zero.mpr hρne, ?_, ?_, ?_⟩
      · rw [hsupp_e₀, he] at hρe₀'
        rw [LinearMap.neg_apply, panelSupportExtensor_swap, map_neg, hρe₀', neg_zero, neg_zero]
      · rw [he] at hρGv'
        rwa [← BodyHingeFramework.hingeRow_swap]
      · intro j
        rcases hwmem' j with hgen | ⟨ρ', hρ'e₀, hwj⟩
        · exact Or.inl hgen
        · refine Or.inr ⟨-ρ', ?_, ?_⟩
          · rw [hsupp_e₀, he] at hρ'e₀
            rw [LinearMap.neg_apply, panelSupportExtensor_swap, map_neg, hρ'e₀, neg_zero, neg_zero]
          · rw [hwj, he, ← BodyHingeFramework.hingeRow_swap]
  -- 5. KT Claim 6.12: a panel `u : Fin 3` and a normal `n'` on whose hinge with the `u`-th normal
  -- `ρ0` does not vanish; the three normals are linearly independent by `P_tri`.
  have htriLI : LinearIndependent K ![na, nb, nc] := hPtri_trans q hq_tri
  obtain ⟨pbar, hp, h0, h1, h2, h3⟩ := exists_homogeneousIncidence_of_normals htriLI
  obtain ⟨u, n', hpair, hgate⟩ :=
    BodyHingeFramework.exists_complementIso_ne_zero_of_homogeneousIncidence
      hρ0ne hp htriLI h0 ⟨h1.1, h1.2.1⟩ ⟨h2.1, h2.2.1⟩ ⟨h3.1, h3.2.1⟩
  rw [← panelSupportExtensor_eq_complementIso_extensor] at hgate
  -- The selector `ends₁` for `u = 0` and `u = 1`: `Q.ends` with `e_a ↦ (v, a)` and `e_b ↦ (v, b)`.
  set ends₁ : β → α × α := Function.update (Function.update Q.ends e_a (v, a)) e_b (v, b)
    with hends₁
  -- `ends₁` is `Q.ends` off `{e_a, e_b}`, so on the links of `Gv`
  -- (`rigidityRows_ofNormals_congr_ends`).
  have hends₁_off : ∀ {e}, e ≠ e_a → e ≠ e_b → ends₁ e = Q.ends e := by
    intro e hea heb
    rw [hends₁, Function.update_of_ne heb, Function.update_of_ne hea]
  have hcongr : (PanelHingeFramework.ofNormals Gv Q.ends q).toBodyHinge.rigidityRows
      = (PanelHingeFramework.ofNormals Gv ends₁ q).toBodyHinge.rigidityRows :=
    PanelHingeFramework.rigidityRows_ofNormals_congr_ends q
      (fun e u w hlink => (hends₁_off (hGv_off hlink).1 (hGv_off hlink).2).symm)
  -- Facts on `Gv` and `G` for `u = 0` and `u = 1`.
  have haVc : a ∈ V(Gv) := by rw [hGv, Graph.vertexSet_removeVertex]; exact ⟨haG, hav⟩
  have hbVc : b ∈ V(Gv) := by rw [hGv, Graph.vertexSet_removeVertex]; exact ⟨hbG, hbv⟩
  have hsplitG : ∀ e u w, G.IsLink e u w → e = e_a ∨ e = e_b ∨ Gv.IsLink e u w := by
    intro e u w hlink
    by_cases hu : u = v
    · subst u; rcases hclv e w hlink with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
    · by_cases hw : w = v
      · subst w; rcases hclv e u hlink.symm with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (by rw [hGv, Graph.removeVertex_isLink]; exact ⟨hlink, hu, hw⟩))
  have hVone : 1 ≤ V(Gv).ncard := by
    rw [hGv, Graph.vertexSet_removeVertex, Set.ncard_sdiff_singleton_of_mem hvG]; omega
  have hVcard : V(G).ncard = V(Gv).ncard + 1 := by
    rw [hGv, Graph.vertexSet_removeVertex, Set.ncard_sdiff_singleton_of_mem hvG]; omega
  -- The values of `ends₁`.
  have hends_ea₁ : ends₁ e_a = (v, a) := by
    rw [hends₁, Function.update_of_ne heab, Function.update_self]
  have hends_eb₁ : ends₁ e_b = (v, b) := by rw [hends₁, Function.update_self]
  have hends_Gv₁ : ∀ e u w, Gv.IsLink e u w → Gv.IsLink e (ends₁ e).1 (ends₁ e).2 := by
    intro e u w hlink
    obtain ⟨hne_a, hne_b⟩ := hGv_off hlink
    rw [hends₁_off hne_a hne_b]
    rcases hrec' e u w (hle e u w hlink) with he | he <;> rw [he]
    · exact hlink
    · exact hlink.symm
  have hne_Gv₁ : ∀ e, Gv.IsLink e (ends₁ e).1 (ends₁ e).2 →
      (PanelHingeFramework.ofNormals Gv ends₁ q).toBodyHinge.supportExtensor e ≠ 0 := by
    intro e hlink
    apply PanelHingeFramework.supportExtensor_ne_zero_of_isGeneralPosition
    · intro x y hxy
      rw [PanelHingeFramework.ofNormals_normal, PanelHingeFramework.ofNormals_normal]
      exact hgp_seed x y hxy
    · rw [PanelHingeFramework.ofNormals_ends]; exact hlink.ne
  -- 6. The three cases of `u`.
  fin_cases u
  · -- `u = 0`: KT's `(G, p_1)`, with `L` in the panel of `a` (`case_III_arm_realization`).
    simp only [show (⟨0, by omega⟩ : Fin 3) = 0 from rfl, Matrix.cons_val_zero] at hpair hgate
    refine PanelHingeFramework.case_III_arm_realization (k := 2) G Gv ends₁ (q := q)
      (v := v) (a := a) (b := b) (e_a := e_a) (e_b := e_b) (n' := n')
      hvVc haVc hbVc hlea hleb hends_ea₁ hends_eb₁ heab hleG hsplitG hends_Gv₁ hne_Gv₁
      hVone hVcard hpair (hgp_seed a b hba.symm) hgate hρ0e₀ ?_ (ιb := _) (w := w) ?_ hw ?_ hdef
    · rw [← hcongr]; exact hρ0Gv
    · rw [Nat.card_fin, hcard]
    · intro j
      rcases hw0mem j with hgen | hcand
      · exact Or.inl (by rw [← hcongr]; exact hgen)
      · exact Or.inr hcand
  · -- `u = 1`: KT's `(G, p_2)`, with `L` in the panel of `b` (`case_III_arm_realization_M2`).
    simp only [show (⟨1, by omega⟩ : Fin 3) = 1 from rfl, Matrix.cons_val_one] at hpair hgate
    refine PanelHingeFramework.case_III_arm_realization_M2 (k := 2) G Gv ends₁ (q := q)
      (v := v) (a := a) (b := b) (e_a := e_a) (e_b := e_b) (n'' := n')
      hvVc haVc hbVc hlea hleb hends_ea₁ hends_eb₁ heab hleG hsplitG hends_Gv₁ hne_Gv₁
      hVone hVcard hpair (hgp_seed a b hba.symm) hgate hρ0e₀ ?_ (ιb := _) (w := w) ?_ hw ?_ hdef
    · rw [← hcongr]; exact hρ0Gv
    · rw [Nat.card_fin, hcard]
    · intro j
      rcases hw0mem j with hgen | hcand
      · exact Or.inl (by rw [← hcongr]; exact hgen)
      · exact Or.inr hcand
  · -- `u = 2`: KT's `(G, p_3)`, with `L` in the panel of `c`, at `G − a`
    -- (`case_III_arm_realization_M3`).
    simp only [show (⟨2, by omega⟩ : Fin 3) = 2 from rfl, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.head_cons] at hpair hgate
    have hebc : e_b ≠ e_c := by
      intro he; subst he
      rcases hleb.eq_and_eq_or_eq_and_eq hlec with ⟨hh, _⟩ | ⟨_, hh⟩
      · exact hav hh.symm
      · exact hba hh
    set ends₃ : β → α × α :=
      Function.update (Function.update (Function.update Q.ends e_c (a, c)) e_a (a, v)) e_b (v, b)
      with hends₃
    have hends₃_ec : ends₃ e_c = (a, c) := by
      simp only [hends₃, Function.update_of_ne hebc.symm, Function.update_of_ne heac.symm,
        Function.update_self]
    have hends₃_ea : ends₃ e_a = (a, v) := by
      rw [hends₃, Function.update_of_ne heab, Function.update_self]
    have hends₃_eb : ends₃ e_b = (v, b) := by rw [hends₃, Function.update_self]
    have hends₃_off : ∀ e, e ≠ e_a → e ≠ e_b → e ≠ e_c → ends₃ e = Q.ends e := by
      intro e hea heb hec
      simp only [hends₃, Function.update_of_ne heb, Function.update_of_ne hea,
        Function.update_of_ne hec]
    have : (G.removeVertex a).Loopless := hGloop.mono (Graph.removeVertex_le G a)
    set qρ : α × Fin 4 → K := fun p => q (Equiv.swap a v p.1, p.2) with hqρ
    have hrecGv : ∀ e x y, Gv.IsLink e x y → Q.ends e = (x, y) ∨ Q.ends e = (y, x) :=
      fun e x y hlink => hrec' e x y (hle e x y hlink)
    -- `hends_Gva` / `hne_Gva` for the `G − a` framework `ofNormals (G − a) ends₃ qρ`.
    have hca_mem : a ∈ V(G) := haG
    have hends_Gva : ∀ e x y, (G.removeVertex a).IsLink e x y →
        (G.removeVertex a).IsLink e (ends₃ e).1 (ends₃ e).2 := by
      intro e x y hlink
      obtain ⟨hGlink, hxa, hya⟩ := Graph.removeVertex_isLink.mp hlink
      by_cases hee_b : e = e_b
      · subst e; rw [hends₃_eb]
        exact Graph.removeVertex_isLink.mpr ⟨hleb, hav.symm, hba⟩
      · -- `e ≠ e_a` and `e ≠ e_c` since both touch `a`.
        have hee_a : e ≠ e_a := by
          intro he; subst e
          rcases hlea.eq_and_eq_or_eq_and_eq hGlink with ⟨_, hh⟩ | ⟨_, hh⟩
          · exact hya hh.symm
          · exact hxa hh.symm
        have hee_c : e ≠ e_c := by
          intro he; subst e
          rcases hlec.eq_and_eq_or_eq_and_eq hGlink with ⟨hh, _⟩ | ⟨hh, _⟩
          · exact hxa hh.symm
          · exact hya hh.symm
        rw [hends₃_off e hee_a hee_b hee_c]
        -- the link avoids `v` (via `hclv`, since `e ∉ {e_a, e_b}`), so it is a `Gv`-link.
        have hxv : x ≠ v := by
          intro h; subst x
          rcases hclv e y hGlink with rfl | rfl <;> [exact hee_a rfl; exact hee_b rfl]
        have hyv : y ≠ v := by
          intro h; subst y
          rcases hclv e x hGlink.symm with rfl | rfl <;> [exact hee_a rfl; exact hee_b rfl]
        have hGvl : Gv.IsLink e x y := by
          rw [hGv, Graph.removeVertex_isLink]; exact ⟨hGlink, hxv, hyv⟩
        rcases hrecGv e x y hGvl with he | he <;> rw [he]
        · exact Graph.removeVertex_isLink.mpr ⟨hGlink, hxa, hya⟩
        · exact Graph.removeVertex_isLink.mpr ⟨hGlink.symm, hya, hxa⟩
    have hGPva : (PanelHingeFramework.ofNormals (G.removeVertex a) ends₃ qρ).IsGeneralPosition := by
      intro x y hxy
      simp only [PanelHingeFramework.ofNormals_normal, hqρ]
      exact hgp_seed _ _ (fun h => hxy ((Equiv.swap a v).injective h))
    have hne_Gva : ∀ e, (G.removeVertex a).IsLink e (ends₃ e).1 (ends₃ e).2 →
        (PanelHingeFramework.ofNormals (G.removeVertex a) ends₃ qρ).toBodyHinge.supportExtensor
          e ≠ 0 := by
      intro e hlink
      refine PanelHingeFramework.supportExtensor_ne_zero_of_isGeneralPosition _ hGPva ?_
      rw [PanelHingeFramework.ofNormals_ends]; exact hlink.ne
    refine PanelHingeFramework.case_III_arm_realization_M3 (k := 2) G Q.ends ends₃ (q := q)
      (v := v) (a := a) (b := b) (c := c) (e_a := e_a) (e_b := e_b) (e_c := e_c) (n''' := n')
      hav.symm hba.symm hbv.symm hca hcv hlea hleb hlec heac hcla hrecGv
      hends₃_ec hends₃_ea hends₃_eb hends₃_off hends_Gva hne_Gva hpair (hgp_seed c a hca)
      hgate hρ0e₀ hρ0Gv (ιb := _) (w := w) ?_ hw ?_ hdef
    · have hGabcard : V(Gab).ncard = V(G).ncard - 1 := by
        rw [hGab, Graph.vertexSet_splitOff, Set.ncard_sdiff_singleton_of_mem hvG]
      rw [Nat.card_fin, hGabcard, Nat.sub_sub]
    · intro j
      rcases hw0mem j with hgen | hcand
      · exact Or.inl hgen
      · exact Or.inr hcand

/-! ## KT eq. (6.22) (`lem:case-III-nested-rank-lower`) -/

/-- **The rank of `G − v` off the zeros of a polynomial** (`lem:case-III-nested-rank-lower`; KT
eq. (6.22), p. 684): let `D = bodyBarDim n = screwDim k` with `1 ≤ k`, let `G` be a simple minimal
`0`-dof-graph with `|V(G)| ≥ 3` and a vertex `v` whose edges are `eₐ : va` and `e_b : vb` (`hclv`),
with `a ≠ b`, and let `e₀ ∉ E(G)`. Suppose that for every `k'`, every minimal `k'`-dof-graph with at
least one and fewer than `|V(G)|` vertices has a panel realization, and a generic full-rank
realization if it is simple (`hIH`). Then for every endpoint selector `ends` that gives each link of
`G.splitOff v a b e₀` its ends in some order (`hrecEnds`), there is a nonzero polynomial `P` in the
normals with `rank R(G − v, q) ≥ D(|V(G.splitOff v a b e₀)| − 1) − (D − 2)` wherever `P(q) ≠ 0`. The
two graphs have the same vertices (`Graph.vertexSet_splitOff`).

The proof, as in the proof of `lem:case-III-nested-rank-lower`. `G − v` is a minimal `k'`-dof-graph
with `k' ≤ D − 2` (`Graph.splitOff_removeVertex_minimalKDof`, `lem:case-III-gap3-minimalKDof`). It
is simple, with at least one and fewer than `|V(G)|` vertices, so `hIH` gives it a generic full-rank
realization, and `exists_rankPolynomial_of_IH_linking` gives `P`, with
`rank R(G − v, q) ≥ D(|V(G − v)| − 1) − k'` wherever `P(q) ≠ 0`. As `k' ≤ D − 2`, this is the bound
(`hV3` gives `|V(G − v)| ≥ 2`, for the arithmetic). Katoh and Tanigawa prove KT eq. (6.22) from the
genericity of the normals (KT footnote 6, p. 684; the remark after
`lem:case-III-nested-rank-lower`); the proofs of `lem:case-III-candidate-dispatch-d3` and
`lem:case-III-chain-discriminator` choose the normals off the zeros of `P` and of the other
polynomials they need. -/
theorem PanelHingeFramework.exists_nested_rankPolynomial_lower_all_k
    [DecidableEq β] [Finite α] [Finite β]
    {n : ℕ} (hk1 : 1 ≤ k) (hn : Graph.bodyBarDim n = screwDim k)
    (G : Graph α β) (v a b : α) (eₐ e_b e₀ : β)
    (hG : G.IsMinimalKDof n 0) (hV3 : 3 ≤ V(G).ncard) (hSimple : G.Simple)
    (hba : b ≠ a) (hav : a ≠ v) (hbv : b ≠ v) (heab : eₐ ≠ e_b)
    (hlea : G.IsLink eₐ v a) (hleb : G.IsLink e_b v b)
    (hclv : ∀ e x, G.IsLink e v x → e = eₐ ∨ e = e_b)
    (he₀ : e₀ ∉ E(G))
    (hIH : ∀ (k' : ℤ) (G' : Graph α β), G'.IsMinimalKDof n k' → V(G').Nonempty →
      V(G').ncard < V(G).ncard →
      (G'.Simple → PanelHingeFramework.HasGenericFullRankRealization K k n G') ∧
        HasPanelRealization K k n G')
    (ends : β → α × α)
    (hrecEnds : ∀ e u w, (G.splitOff v a b e₀).IsLink e u w → ends e = (u, w) ∨ ends e = (w, u)) :
    ∃ P : MvPolynomial (α × Fin (k + 2)) K,
      P ≠ 0 ∧
      ∀ q : α × Fin (k + 2) → K, MvPolynomial.eval q P ≠ 0 →
        screwDim k * (V(G.splitOff v a b e₀).ncard - 1) - (screwDim k - 2)
          ≤ Module.finrank K (Submodule.span K
              (PanelHingeFramework.ofNormals (G.removeVertex v) ends
                q).toBodyHinge.rigidityRows) := by
  have hD3 : 3 ≤ Graph.bodyBarDim n := hn ▸ three_le_screwDim hk1
  -- `hle`: every `(G.removeVertex v)`-link is a `(G.splitOff v a b e₀)`-link.
  have hle : ∀ e u w, (G.removeVertex v).IsLink e u w → (G.splitOff v a b e₀).IsLink e u w := by
    intro e u w hlink
    rw [Graph.removeVertex_isLink] at hlink
    obtain ⟨hGlink, hunev, hwnev⟩ := hlink
    have hee₀ : e ≠ e₀ := fun h => he₀ (h ▸ hGlink.edge_mem)
    rw [Graph.splitOff_isLink]
    exact Or.inl ⟨hee₀, hGlink, hunev, hwnev⟩
  -- `hends'`: `ends` records links of `G.removeVertex v`.
  have hends' : ∀ e u w, (G.removeVertex v).IsLink e u w →
      (G.removeVertex v).IsLink e (ends e).1 (ends e).2 := by
    intro e u w hlink
    rcases hrecEnds e u w (hle e u w hlink) with h | h
    · rw [h]; exact hlink
    · rw [h]; exact hlink.symm
  -- `hcard`: `V(G.splitOff v a b e₀).ncard = V(G.removeVertex v).ncard`.
  have hcard : V(G.splitOff v a b e₀).ncard = V(G.removeVertex v).ncard := by
    rw [Graph.vertexSet_splitOff, Graph.vertexSet_removeVertex]
  obtain ⟨hGvmin, _hk'nn, hk'le⟩ :=
    Graph.splitOff_removeVertex_minimalKDof (by omega : 2 ≤ Graph.bodyBarDim n)
      hba.symm hav hbv heab hlea hleb hclv he₀ hG
  have hGvSimple : (G.removeVertex v).Simple := hSimple.mono (Graph.removeVertex_le G v)
  have hGvne : V(G.removeVertex v).Nonempty :=
    ⟨a, by rw [Graph.vertexSet_removeVertex]; exact ⟨hlea.right_mem, hav⟩⟩
  have hGvlt : V(G.removeVertex v).ncard < V(G).ncard := by
    rw [Graph.vertexSet_removeVertex,
      Set.ncard_sdiff_singleton_of_mem (hlea.left_mem : v ∈ V(G))]; omega
  have hQv : PanelHingeFramework.HasGenericFullRankRealization K k n (G.removeVertex v) :=
    (hIH _ (G.removeVertex v) hGvmin hGvne hGvlt).1 hGvSimple
  have hGvloop : (G.removeVertex v).Loopless := hGvSimple.toLoopless
  -- The polynomial `P` of `exists_rankPolynomial_of_IH_linking` for the realization of `G − v`.
  obtain ⟨N, hNeq, P, hPne, hPtrans⟩ :=
    PanelHingeFramework.exists_rankPolynomial_of_IH_linking (G.removeVertex v) ends hQv
      hGvloop hends'
  -- The arithmetic `D(|V(Gab)| − 1) − (D − 2) ≤ N`, which does not involve `q`.
  have hGvne1 : 1 ≤ V(G.splitOff v a b e₀).ncard :=
    hcard ▸ (Set.ncard_pos (Set.toFinite _)).2 hGvne
  have hDge2 : 2 ≤ screwDim k := two_le_screwDim hk1
  have hGab2 : 2 ≤ V(G.splitOff v a b e₀).ncard := by
    rw [hcard, Graph.vertexSet_removeVertex,
      Set.ncard_sdiff_singleton_of_mem (hlea.left_mem : v ∈ V(G))]; omega
  have hcardZ : (V(G.splitOff v a b e₀).ncard : ℤ) = V(G.removeVertex v).ncard := by
    exact_mod_cast hcard
  have hD_eq : (screwDim k : ℤ) = Graph.bodyBarDim n := by omega
  have hDsub : screwDim k - 2 ≤ screwDim k * (V(G.splitOff v a b e₀).ncard - 1) :=
    screwDim_sub_two_le_mul hGab2
  have hLHSN : screwDim k * (V(G.splitOff v a b e₀).ncard - 1) - (screwDim k - 2) ≤ N := by
    apply Nat.cast_le (α := ℤ) |>.mp
    rw [Nat.cast_sub hDsub, Nat.cast_mul, Nat.cast_sub hGvne1, Nat.cast_sub hDge2]
    simp only [Nat.cast_one, Nat.cast_ofNat]
    rw [← hcardZ] at hNeq
    linarith [hNeq, hk'le, hD_eq]
  -- At a non-root `q` of `P`, `hPtrans` and `hLHSN` give the bound.
  exact ⟨P, hPne, fun q hPeval => le_trans hLHSN (hPtrans q hPeval)⟩

/-! ## The case of a chain: the form `r` at `G_1` and the panels

Steps of `lem:case-III-chain-discriminator`. For a chain `v₀v₁⋯v_d` of length `d`
(`Graph.ChainData`), Katoh and Tanigawa split off once, at `v₁` along `v₀v₂`, and take the form `r`
of KT eq. (6.52) at the new edge `v₀v₂` of `G_1`, as for `d = 3` (KT pp. 692–693).
`chainData_split_w6b_gates` gives it at a split `(v, a, b)`, with normals off the zeros of a given
polynomial. The `d` panels of KT eq. (6.67) are those of `u_0 = v₀` and `u_i = v_{i+1}`;
`Graph.ChainData.candidatePanel` indexes them by `Fin (k + 1)`, as `d = k + 1`
(`Graph.ChainData.d_eq_kAdd`). -/

/-- **The form `r` and the bottom rows at a split, off the zeros of a given polynomial** (a step of
`lem:case-III-chain-discriminator`): let `D = bodyBarDim n = screwDim k` with `1 ≤ k`, let `G` be
loopless, `a ≠ b` vertices of `G` other than `v`, `e₀ ∉ E(G)`, and let `Gab = G.splitOff v a b e₀`
have deficiency `0` and a generic full-rank realization (`hsplitGP`). Suppose that for every
selector that gives each link of `Gab` its ends in some order there is a nonzero polynomial `P` with
`rank R(G − v, q) ≥ D(|V(Gab)| − 1) − (D − 2)` wherever `P(q) ≠ 0` (`h622lb`, as
`exists_nested_rankPolynomial_lower_all_k` gives it), and let `Pu ≠ 0` be a polynomial in the
normals. Then there are normals `q` with `Pu(q) ≠ 0`, a selector `ends` that gives each link of
`Gab` its ends in some order, with `ofNormals Gab ends q` in general position, a nonzero linear form
`ρ` on `K^D` with `ρ(C(q(a), q(b))) = 0` whose row `hingeRow a b ρ` lies in the row space of
`R(G − v, q)`, and `D(|V(Gab)| − 1)` linearly independent forms `w`, each a row of `R(G − v, q)` or
a form `hingeRow a b ρ'` with `ρ'(C(q(a), q(b))) = 0`. At the split at `v₁` along `v₀v₂`, these are
KT's form `r` and rows that span the row space of `R(G_1 ∖ (v₀v₂)_{i*}, q_1)` (KT eqs. (6.51) and
(6.52), p. 693). Moreover, `ρ = ∑_j lamAB j • rab j` for forms `rab j` in the hinge-row block of
`e₀`, and `hingeRow a b ρ` is a combination of rows of `R(G − v, q)` at links of `G − v`, grouped by
edge, which the proof of `lem:case-III-chain-dispatch` reads at the edge `v_i v_{i+1}` (KT
eq. (6.66), `lem:case-III-chain-eq666`).

The proof, as in the proof of `lem:case-III-chain-discriminator`, and as
`case_III_candidate_dispatch` takes `ρ` and `w`. With the selector `Q.ends` of the realization of
`Gab`, three nonzero polynomials are fixed before the normals: that of
`exists_rankPolynomial_of_IH_linking` for `Gab`, that of `h622lb` at `Q.ends` and that of
`exists_generalPosition_polynomial`; `q` is a non-root of their product with `Pu`
(`MvPolynomial.exists_eval_ne_zero₄`). At `q`, the first and the deficiency bound
(`lem:relative-deficiency-rank-bound`) make `ofNormals Gab Q.ends q` infinitesimally rigid on
`V(Gab)` (KT eq. (6.18)), and `exists_candidateRow_bottomRows_of_rigidOn`, with the second (KT
eq. (6.22)), gives `ρ`, `w`, `rab` and the combination, which the proof states at the orientation
`(a, b)`, with `−ρ` and `−rab` if `Q.ends e₀ = (b, a)`. Its user
`exists_shared_redundancy_and_matched_candidate` takes for `Pu` the polynomial of
`exists_tupleLI_polynomial` that makes the normals of the panels of KT eq. (6.67) linearly
independent. -/
theorem PanelHingeFramework.chainData_split_w6b_gates [Infinite K]
    [Finite α] [Finite β]
    (hk1 : 1 ≤ k) (G : Graph α β) (v a b : α) (e₀ : β)
    (hav : a ≠ v) (hbv : b ≠ v) (hba : b ≠ a)
    (haG : a ∈ V(G)) (hbG : b ∈ V(G))
    (he₀ : e₀ ∉ E(G)) (hGloop : G.Loopless)
    -- A nonzero polynomial in the normals, fixed before them: the normals `q` of the conclusion are
    -- off its zeros. `exists_shared_redundancy_and_matched_candidate` passes that of
    -- `exists_tupleLI_polynomial`; a caller that needs no condition passes `1`.
    (Pu : MvPolynomial (α × Fin (k + 2)) K) (hPu : Pu ≠ 0)
    -- The bound of KT eq. (6.22) at `G − v` off the zeros of a polynomial, for every selector that
    -- gives each link of `Gab` its ends, as `exists_nested_rankPolynomial_lower_all_k` gives it.
    (h622lb : ∀ (ends : β → α × α),
      (∀ e u w, (G.splitOff v a b e₀).IsLink e u w → ends e = (u, w) ∨ ends e = (w, u)) →
      ∃ P : MvPolynomial (α × Fin (k + 2)) K, P ≠ 0 ∧
        ∀ q : α × Fin (k + 2) → K, MvPolynomial.eval q P ≠ 0 →
          screwDim k * (V(G.splitOff v a b e₀).ncard - 1) - (screwDim k - 2)
            ≤ Module.finrank K (Submodule.span K
                (PanelHingeFramework.ofNormals (G.removeVertex v) ends
                  q).toBodyHinge.rigidityRows))
    {n : ℕ} (hn : Graph.bodyBarDim n = screwDim k)
    (hdef_Gab : (G.splitOff v a b e₀).deficiency n = 0)
    (hsplitGP : PanelHingeFramework.HasGenericFullRankRealization K k n (G.splitOff v a b e₀)) :
    ∃ (q : α × Fin (k + 2) → K) (ends : β → α × α)
      (ρ : Module.Dual K (ScrewSpace K k))
      (w : Fin (screwDim k * (V(G.splitOff v a b e₀).ncard - 1)) →
        Module.Dual K (α → ScrewSpace K k))
      (lamAB : Fin (screwDim k - 1) → K)
      (rab : Fin (screwDim k - 1) → Module.Dual K (ScrewSpace K k)),
      -- `ofNormals Gab ends q` is in general position, and `ends` records the links of `Gab`
      (PanelHingeFramework.ofNormals (G.splitOff v a b e₀) ends q).IsGeneralPosition ∧
      PanelHingeFramework.RecordsLinks (G.splitOff v a b e₀) ends ∧
      -- the form `ρ` and the bottom rows `w`, at the orientation `(a, b)`
      ρ ≠ 0 ∧
      ρ (panelSupportExtensor (fun i => q (a, i)) (fun i => q (b, i))) = 0 ∧
      BodyHingeFramework.hingeRow a b ρ ∈ Submodule.span K
        (PanelHingeFramework.ofNormals (G.removeVertex v) ends q).toBodyHinge.rigidityRows ∧
      LinearIndependent K w ∧
      (∀ j, w j ∈
          (PanelHingeFramework.ofNormals (G.removeVertex v) ends q).toBodyHinge.rigidityRows ∨
        ∃ ρ' : Module.Dual K (ScrewSpace K k),
          ρ' (panelSupportExtensor (fun i => q (a, i)) (fun i => q (b, i))) = 0 ∧
          w j = BodyHingeFramework.hingeRow a b ρ') ∧
      -- `ρ = ∑_j lamAB j • rab j`, with each `rab j` in the hinge-row block of `e₀`
      (∀ j, rab j ∈ BodyHingeFramework.hingeRowBlock
        (PanelHingeFramework.ofNormals (G.splitOff v a b e₀) ends q).toBodyHinge e₀) ∧
      ρ = ∑ j, lamAB j • rab j ∧
      -- `hingeRow a b ρ` as a combination of rows of `R(G − v, q)` at links `evGv j` of `G − v`,
      -- with forms `rvGv j` in the hinge-row block of `evGv j` (KT eq. (6.52), grouped by edge for
      -- KT eq. (6.66))
      (∃ (nGv : ℕ) (cGv : Fin nGv → K) (evGv : Fin nGv → β) (uvGv vvGv : Fin nGv → α)
          (rvGv : Fin nGv → Module.Dual K (ScrewSpace K k)),
        (∀ j, (G.removeVertex v).IsLink (evGv j) (uvGv j) (vvGv j)) ∧
        (∀ j, rvGv j ∈ ((PanelHingeFramework.ofNormals (G.removeVertex v) ends q).toBodyHinge
          ).hingeRowBlock (evGv j)) ∧
        BodyHingeFramework.hingeRow a b ρ
          = ∑ j, cGv j • BodyHingeFramework.hingeRow (uvGv j) (vvGv j) (rvGv j)) ∧
      -- the normals are off the zeros of `Pu`
      MvPolynomial.eval q Pu ≠ 0 := by
  classical
  have : Fintype α := Fintype.ofFinite α
  set Gab := G.splitOff v a b e₀ with hGab
  set Gv := G.removeVertex v with hGv
  -- `Gab` is loopless: a surviving `G`-edge inherits `G`'s looplessness, the fresh `e₀` joins the
  -- distinct `a ≠ b`.
  have hGabloop : Gab.Loopless := by
    rw [Graph.loopless_iff_forall_ne_of_adj]
    rintro x y ⟨e, hlink⟩
    rw [hGab, Graph.splitOff_isLink] at hlink
    rcases hlink with ⟨_, hGlink, _, _⟩ | ⟨_, _, _, _, _, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩
    · exact hGlink.ne
    · exact hba.symm
    · exact hba
  -- 1. The selector `Q.ends` of the realization of `Gab`. The three polynomials are fixed before
  -- the normals `q`, a non-root of their product with `Pu`, as in `case_III_candidate_dispatch`.
  obtain ⟨Q, _, _, _, hQrec⟩ := id hsplitGP
  have hrec' : ∀ e u w, Gab.IsLink e u w → Q.ends e = (u, w) ∨ Q.ends e = (w, u) := by
    intro e u w he
    rcases hQrec e u w he with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl (Prod.ext h1 h2)
    · exact Or.inr (Prod.ext h1 h2)
  have hends_Gab : ∀ e u w, Gab.IsLink e u w → Gab.IsLink e (Q.ends e).1 (Q.ends e).2 := by
    intro e u w he
    rcases hrec' e u w he with h | h <;> rw [h]
    · exact he
    · exact he.symm
  have hne' : V(Gab).Nonempty := ⟨a, by rw [hGab, Graph.vertexSet_splitOff]; exact ⟨haG, by
    simp [hav]⟩⟩
  have h1_Gab : 1 ≤ V(Gab).ncard := (Set.ncard_pos (Set.toFinite _)).2 hne'
  -- Factor 1 (`P_ab`): the rank polynomial of `Gab` at `Q.ends`, for KT eq. (6.18).
  obtain ⟨N, hNeq, P_ab, hP_abne, hP_abtrans⟩ :=
    PanelHingeFramework.exists_rankPolynomial_of_IH_linking Gab Q.ends hsplitGP hGabloop hends_Gab
  -- Factor 2 (`P_v`): the polynomial of KT eq. (6.22) for `Gv` at `Q.ends`, from `h622lb`.
  obtain ⟨P_v, hP_vne, hP_vtrans⟩ := h622lb Q.ends hrec'
  -- Factor 3 (`Q_gp`): the general-position polynomial for `Gab` at `Q.ends`.
  obtain ⟨Qgp, hQgp_mc, hQgp_pos⟩ := exists_generalPosition_polynomial (K := K) (k := k) Gab Q.ends
  have hQgp_ne : Qgp ≠ 0 := by
    obtain ⟨f, hf⟩ := Countable.exists_injective_of_infinite α K
    exact fun h => hQgp_mc f hf (by rw [h, map_zero])
  -- Normals `q` off the zeros of the three factors and of `Pu`.
  obtain ⟨q, hq_ab, hq_v, hq_gp, hq_u⟩ :=
    MvPolynomial.exists_eval_ne_zero₄ hP_abne hP_vne hQgp_ne hPu
  -- General position of `ofNormals Gab Q.ends q` (from `Q_gp`).
  have hgp' : (PanelHingeFramework.ofNormals Gab Q.ends q).IsGeneralPosition := hQgp_pos q hq_gp
  -- Infinitesimal rigidity of `ofNormals Gab Q.ends q` (KT eq. (6.18)): `P_ab` gives `N ≤ rank`,
  -- and the deficiency bound (`lem:relative-deficiency-rank-bound`) at `def = 0` the reverse.
  have hFgraph : (PanelHingeFramework.ofNormals Gab Q.ends q).toBodyHinge.graph = Gab := by
    rw [PanelHingeFramework.toBodyHinge_graph, PanelHingeFramework.ofNormals_graph]
  have hFC : ∀ e u w, (PanelHingeFramework.ofNormals Gab Q.ends q).toBodyHinge.graph.IsLink e u w →
      (PanelHingeFramework.ofNormals Gab Q.ends q).toBodyHinge.supportExtensor e ≠ 0 := by
    intro e u w hlink
    rw [hFgraph] at hlink
    refine PanelHingeFramework.supportExtensor_ne_zero_of_isGeneralPosition _ hgp' ?_
    rw [PanelHingeFramework.ofNormals_ends]
    exact (hends_Gab e u w hlink).ne
  have hB2 := BodyHingeFramework.finrank_span_rigidityRows_add_deficiency_le
    (PanelHingeFramework.ofNormals Gab Q.ends q).toBodyHinge hn (by rw [hFgraph]; exact hne') hFC
  rw [hFgraph, hdef_Gab, sub_zero] at hB2
  rw [hdef_Gab, sub_zero] at hNeq
  have hNle := hP_abtrans q hq_ab
  have hrig' : (PanelHingeFramework.ofNormals Gab Q.ends q).toBodyHinge.IsInfinitesimallyRigidOn
      V(Gab) := by
    have hiff := BodyHingeFramework.isInfinitesimallyRigidOn_vertexSet_iff_finrank_span_rigidityRows
      (PanelHingeFramework.ofNormals Gab Q.ends q).toBodyHinge (by rw [hFgraph]; exact hne')
    rw [hFgraph] at hiff
    rw [hiff]
    have hfin_le : Module.finrank K (Submodule.span K
        (PanelHingeFramework.ofNormals Gab Q.ends q).toBodyHinge.rigidityRows) ≤ N := by
      have : (Module.finrank K (Submodule.span K
          (PanelHingeFramework.ofNormals Gab Q.ends q).toBodyHinge.rigidityRows) : ℤ) ≤ N := by
        rw [hNeq]; exact hB2
      exact_mod_cast this
    rw [le_antisymm hfin_le hNle]
    zify [h1_Gab]; linarith [hNeq]
  -- 2. Facts on `Gab` and `Gv`.
  have he₀ab : Gab.IsLink e₀ a b := by
    rw [hGab, Graph.splitOff_isLink]
    exact Or.inr ⟨rfl, hav, hbv, haG, hbG, Or.inl ⟨rfl, rfl⟩⟩
  have hle : ∀ e u w, Gv.IsLink e u w → Gab.IsLink e u w := by
    intro e u w hlink
    rw [hGv, Graph.removeVertex_isLink] at hlink
    obtain ⟨hGlink, hunev, hwnev⟩ := hlink
    have hee₀ : e ≠ e₀ := fun h => he₀ (h ▸ hGlink.edge_mem)
    rw [hGab, Graph.splitOff_isLink]
    exact Or.inl ⟨hee₀, hGlink, hunev, hwnev⟩
  have hsplit : ∀ e u w, Gab.IsLink e u w → Gv.IsLink e u w ∨ e = e₀ := by
    intro e u w hlink
    rw [hGab, Graph.splitOff_isLink] at hlink
    rcases hlink with ⟨hee₀, hGlink, hunev, hwnev⟩ | ⟨he, _⟩
    · exact Or.inl (by rw [hGv, Graph.removeVertex_isLink]; exact ⟨hGlink, hunev, hwnev⟩)
    · exact Or.inr he
  -- `hrecGab`: `Q.ends` records the links of `Gab`.
  have hrecGab := PanelHingeFramework.recordsLinks_iff_forall_isLink.mpr hends_Gab
  -- 3. The form `ρ`, the bottom rows `w`, the forms `rab` and the combination
  -- (`exists_candidateRow_bottomRows_of_rigidOn`).
  have hD : (2 : ℕ) ≤ screwDim k := two_le_screwDim hk1
  have huv : (Q.ends e₀).1 ≠ (Q.ends e₀).2 := by
    rcases hrec' e₀ a b he₀ab with he | he <;> rw [he]
    · exact hba.symm
    · exact hba
  have hne₀ : (PanelHingeFramework.ofNormals Gab Q.ends q).toBodyHinge.supportExtensor e₀ ≠ 0 := by
    apply PanelHingeFramework.supportExtensor_ne_zero_of_isGeneralPosition _ hgp'
    rw [PanelHingeFramework.ofNormals_ends]; exact huv
  have he₀' : Gab.IsLink e₀ (Q.ends e₀).1 (Q.ends e₀).2 := by
    rcases hrec' e₀ a b he₀ab with he | he <;> rw [he]
    · exact he₀ab
    · exact he₀ab.symm
  obtain ⟨ρ, w, lamAB, rab, hρne, hρe₀', hρGv', hw, hwmem', hrab_blk, hρ_lam, hedgeGv⟩ :=
    BodyHingeFramework.exists_candidateRow_bottomRows_of_rigidOn (Gab := Gab) (Gv := Gv)
      (ends := Q.ends) (q := q) (e₀ := e₀) hD huv hne₀ he₀' hle hsplit hne' hrig'
      (hP_vtrans q hq_v)
  -- 4. The form and the rows at the orientation `(a, b)`, with `-ρ` if `Q.ends e₀ = (b, a)`.
  set na := (fun i => q (a, i)) with hna
  set nb := (fun i => q (b, i)) with hnb
  -- The hinge of `e₀` as a `panelSupportExtensor`.
  have hsupp_e₀ : ∀ (r : Module.Dual K (ScrewSpace K k)),
      r ((PanelHingeFramework.ofNormals Gab Q.ends q).toBodyHinge.supportExtensor e₀) =
        r (panelSupportExtensor (fun i => q ((Q.ends e₀).1, i))
          (fun i => q ((Q.ends e₀).2, i))) := by
    intro r
    simp only [PanelHingeFramework.toBodyHinge_supportExtensor, PanelHingeFramework.ofNormals_ends,
      PanelHingeFramework.ofNormals_normal]
  refine ⟨q, Q.ends, ?_⟩
  rcases hrec' e₀ a b he₀ab with he | he
  · -- recorded `(a, b)`: take `ρ` as is.
    refine ⟨ρ, w, lamAB, rab, hgp', hrecGab, hρne, ?_, ?_, hw, ?_, hrab_blk, hρ_lam, ?_, hq_u⟩
    · rw [hsupp_e₀, he] at hρe₀'; exact hρe₀'
    · rw [he] at hρGv'; exact hρGv'
    · intro j
      rcases hwmem' j with hgen | ⟨ρ', hρ'e₀, hwj⟩
      · exact Or.inl hgen
      · refine Or.inr ⟨ρ', ?_, by rw [hwj, he]⟩
        rw [hsupp_e₀, he] at hρ'e₀; exact hρ'e₀
    · -- the combination grouped by edge: as `Q.ends e₀ = (a, b)`, `hingeRow a b ρ` is the row
      -- `hingeRow (Q.ends e₀).1 (Q.ends e₀).2 ρ` of `exists_candidateRow_bottomRows_of_rigidOn`.
      obtain ⟨nGv, cGv, evGv, uvGv, vvGv, rvGv, hlinkGv, hrvGv, hcombGv⟩ := hedgeGv
      exact ⟨nGv, cGv, evGv, uvGv, vvGv, rvGv, hlinkGv, hrvGv, by rw [he] at hcombGv; exact hcombGv⟩
  · -- recorded `(b, a)`: take `-ρ` (`hingeRow b a (-ρ) = hingeRow a b ρ`) and `-rab` (the block is
    -- a subspace, and `-ρ = Σ_j λ_j (-rab j)`).
    refine ⟨-ρ, w, lamAB, fun j => -rab j, hgp', hrecGab, neg_ne_zero.mpr hρne, ?_, ?_, hw, ?_,
      fun j => (PanelHingeFramework.ofNormals Gab Q.ends q).toBodyHinge.hingeRowBlock e₀ |>.neg_mem
        (hrab_blk j), ?_, ?_, hq_u⟩
    · rw [hsupp_e₀, he] at hρe₀'
      rw [LinearMap.neg_apply, panelSupportExtensor_swap, map_neg, hρe₀', neg_zero, neg_zero]
    · rw [he] at hρGv'
      rwa [← BodyHingeFramework.hingeRow_swap]
    · intro j
      rcases hwmem' j with hgen | ⟨ρ', hρ'e₀, hwj⟩
      · exact Or.inl hgen
      · refine Or.inr ⟨-ρ', ?_, ?_⟩
        · rw [hsupp_e₀, he] at hρ'e₀
          rw [LinearMap.neg_apply, panelSupportExtensor_swap, map_neg, hρ'e₀, neg_zero, neg_zero]
        · rw [hwj, he, ← BodyHingeFramework.hingeRow_swap]
    · rw [hρ_lam, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun j _ => (smul_neg _ _).symm
    · -- the combination grouped by edge: as `Q.ends e₀ = (b, a)`,
      -- `hingeRow a b (-ρ) = hingeRow b a ρ` (`hingeRow_swap`) is the row of
      -- `exists_candidateRow_bottomRows_of_rigidOn`, and the combination is unchanged.
      obtain ⟨nGv, cGv, evGv, uvGv, vvGv, rvGv, hlinkGv, hrvGv, hcombGv⟩ := hedgeGv
      refine ⟨nGv, cGv, evGv, uvGv, vvGv, rvGv, hlinkGv, hrvGv, ?_⟩
      rw [he] at hcombGv
      rw [BodyHingeFramework.hingeRow_swap a b (-ρ), neg_neg]; exact hcombGv

/-- **The length of a chain is `k + 1`** (a step of `lem:case-III-chain-discriminator`): if
`bodyBarDim n = screwDim k`, a chain `cd : G.ChainData n` has length `cd.d = k + 1`. So the `d`
panels of KT eq. (6.67) (p. 698), one for each of the `d` frameworks, are `k + 1` hyperplanes in the
space `K^{k+2}` of the normals; `Graph.ChainData.candidatePanel` indexes them by `Fin (k + 1)`, as
`exists_chainData_discriminator_pick_of_LI` takes them.

The proof. `cd.d = n` (`d_eq`), and `n = k + 1` (`Graph.eq_add_one_of_bodyBarDim_eq_screwDim`). -/
theorem _root_.Graph.ChainData.d_eq_kAdd {G : Graph α β} {n : ℕ} (cd : G.ChainData n)
    (hn : Graph.bodyBarDim n = screwDim k) : cd.d = k + 1 :=
  cd.d_eq.trans (Graph.eq_add_one_of_bodyBarDim_eq_screwDim hn)

/-- **The vertices `u_0, …, u_{d−1}` of the panels, indexed by `Fin (k + 1)`** (a step of
`lem:case-III-chain-discriminator`): `Graph.ChainData.candidateVtx`, the map `i ↦ u_i` with
`u_0 = v₀` and `u_i = v_{i+1}` (KT eq. (6.67), p. 698), composed with `Fin.cast` along
`cd.d = k + 1` (`Graph.ChainData.d_eq_kAdd`). It is the injective `cand` at which
`exists_shared_redundancy_and_matched_candidate` applies `exists_tupleLI_polynomial` and
`exists_chainData_discriminator_pick_of_LI`. -/
def _root_.Graph.ChainData.candidatePanel {G : Graph α β} {n : ℕ} (cd : G.ChainData n)
    (hn : Graph.bodyBarDim n = screwDim k) : Fin (k + 1) → α :=
  cd.candidateVtx ∘ Fin.cast (cd.d_eq_kAdd hn).symm

/-- `candidatePanel hn u` is `candidateVtx` at the index `Fin.cast (cd.d_eq_kAdd hn).symm u` of
`Fin cd.d`, by definition (a step of `lem:case-III-chain-discriminator`): it carries the panel that
`exists_chainData_discriminator_pick_of_LI` chooses to its index among the `d` frameworks. -/
lemma _root_.Graph.ChainData.candidatePanel_apply {G : Graph α β} {n : ℕ} (cd : G.ChainData n)
    (hn : Graph.bodyBarDim n = screwDim k) (u : Fin (k + 1)) :
    cd.candidatePanel hn u = cd.candidateVtx (Fin.cast (cd.d_eq_kAdd hn).symm u) := rfl

/-- **The vertices `u_i` are distinct** (a step of `lem:case-III-chain-discriminator`):
`candidatePanel hn` is injective, by `Graph.ChainData.candidateVtx_injective` and the injectivity of
`Fin.cast`. -/
lemma _root_.Graph.ChainData.candidatePanel_injective {G : Graph α β} {n : ℕ} (cd : G.ChainData n)
    (hn : Graph.bodyBarDim n = screwDim k) : Function.Injective (cd.candidatePanel hn) :=
  cd.candidateVtx_injective.comp (Fin.cast_injective _)

/-! ## The frameworks of a chain at a split

`chainData_interior_realization_hρGv` is a step of `lem:case-III-chain-dispatch`: Katoh and
Tanigawa's framework `(G, p_i)` for `2 ≤ i`, built from `(G_i, q_i)` (KT pp. 693–697). -/

/-- **The `i`-th framework of a chain, for `2 ≤ i`** (a step of `lem:case-III-chain-dispatch`): let
`cd` be a chain in `G`, of deficiency `0`, with `2 ≤ i`, `v = vtx i.castSucc`, `a = vtx i.succ`,
`b = vtx (i − 1).castSucc`, `σᵢ = cd.shiftPerm i.castSucc` and `qᵢ = q ∘ σᵢ`
(`fun p => q (σᵢ p.1, p.2)`), so that `qᵢ(a) = q(a)` and `qᵢ(b) = q(v)`
(`Graph.ChainData.seedShift_succ_castSucc`, `Graph.ChainData.seedShift_pred_castSucc`). Let the
selector `endsσρ₁` agree with `ends₀` off `edge i` and `edge (i − 1)` (`hoff`), give these two edges
the ends `(v, a)` and `(v, b)`, and give each link of `G − v` its ends, with nonzero hinges in
`ofNormals (G − v) endsσρ₁ qᵢ`. Let `ends₀` give each link of `G_1 = G.splitOff v₁ v₂ v₀ e₀` its
ends in some order (`hrec'`). Suppose that `q(a), n'` and `q(a), q(v)` are linearly independent,
that the form `ρ₀` satisfies `ρ₀(C(q(a), n')) ≠ 0` and vanishes on `C(qᵢ(a), qᵢ(b))`, that
`hingeRow a b (−ρ₀)` lies in the row space of `R(G − v, qᵢ)` with the selector `ends₀`, and that
`D(|V(G)| − 2)` linearly independent forms `w` are each a row of `R(G − v, qᵢ)` with the selector
`Graph.ChainData.candidateEnds i ends₀` or a form `hingeRow a b ρ'` with `ρ'` vanishing on
`C(qᵢ(a), qᵢ(b))`. Then `G` has a generic full-rank realization. This is the framework `(G, p_i)` of
the proof of `lem:case-III-chain-dispatch`, built from `(G_i, q_i)` with `vᵢ`, `vᵢ₊₁` and `vᵢ₋₁` in
the roles of `v`, `a` and `b` and the form `−r` (KT eqs. (6.56)–(6.59), p. 694, and (6.64), p. 697).
For `d = 3` and `i = 2`, `σ₂` exchanges `v₁` and `v₂`, as `case_III_arm_realization_M3` exchanges
`a` and `v`.

The proof. The edges `edge i` and `edge (i − 1)` meet `v`, so they are not links of `G − v`, and the
rows of `R(G − v, qᵢ)` with the selectors `ends₀` and `endsσρ₁` are the same
(`rigidityRows_ofNormals_congr_ends`). Those with `candidateEnds i ends₀` and with `endsσρ₁` are the
same too, as both give each link of `G − v` its ends in some order
(`rigidityRows_ofNormals_congr_ends_swap`; `Graph.ChainData.candidateEnds_records_splitOff_isLink`,
from `hrec'`). Then `case_III_arm_realization`, at `qᵢ` and `−ρ₀`, gives the realization. -/
theorem PanelHingeFramework.chainData_interior_realization_hρGv [Infinite K]
    [DecidableEq α] [DecidableEq β] [Finite α] [Finite β]
    {G : Graph α β} {n : ℕ} (cd : G.ChainData n) (i : Fin cd.d) (h2i : 2 ≤ (i : ℕ))
    {ends₀ : β → α × α} {q : α × Fin (k + 2) → K}
    {ρ₀ : Module.Dual K (ScrewSpace K k)} {n' : Fin (k + 2) → K}
    -- The selector of the framework, built by `chainData_dispatch_interior` as `ends₀` with the two
    -- edges `edge i` and `edge (i − 1)` at `vᵢ` given the ends `(v, a)` and `(v, b)`. Neither edge
    -- is a link of `G − vᵢ`, so on its links `endsσρ₁` is `ends₀` (`hoff`).
    (endsσρ₁ : β → α × α)
    (hoff : ∀ e, e ≠ cd.edge i → e ≠ cd.edge ⟨(i : ℕ) - 1, by have := i.isLt; omega⟩ →
      endsσρ₁ e = ends₀ e)
    -- `endsσρ₁` gives the two edges at `v = vtx i.castSucc` their ends, from `v`:
    (hends_ea : endsσρ₁ (cd.edge i) = (cd.vtx i.castSucc, cd.vtx i.succ))
    (hends_eb : endsσρ₁ (cd.edge ⟨(i : ℕ) - 1, by have := i.isLt; omega⟩)
      = (cd.vtx i.castSucc, cd.vtx (⟨(i : ℕ) - 1, by have := i.isLt; omega⟩ : Fin cd.d).castSucc))
    -- `endsσρ₁` gives each link of `G − vᵢ` its ends:
    (hends_Gv : ∀ e u w, (G.removeVertex (cd.vtx i.castSucc)).IsLink e u w →
      (G.removeVertex (cd.vtx i.castSucc)).IsLink e (endsσρ₁ e).1 (endsσρ₁ e).2)
    -- the hinges at the links of `G − vᵢ` are nonzero:
    (hne_Gv : ∀ e, (G.removeVertex (cd.vtx i.castSucc)).IsLink e (endsσρ₁ e).1 (endsσρ₁ e).2 →
      (PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx i.castSucc)) endsσρ₁
        (fun p => q (cd.shiftPerm i.castSucc p.1, p.2))).toBodyHinge.supportExtensor e ≠ 0)
    -- the normal `n'` at the panel of `a = vtx i.succ`, on whose hinge with `q(a)` `ρ₀` does not
    -- vanish:
    (hLn : LinearIndependent K ![(fun j => q (cd.vtx i.succ, j)), n'])
    -- `q(a)` and `q(v)` are linearly independent, as `qᵢ(b) = q(v)` (`seedShift_pred_castSucc`):
    (hgab : LinearIndependent K
      ![(fun j => q (cd.vtx i.succ, j)), (fun j => q (cd.vtx i.castSucc, j))])
    (hρgate : ρ₀ (panelSupportExtensor (fun j => q (cd.vtx i.succ, j)) n') ≠ 0)
    -- `ρ₀` vanishes on the hinge `C(qᵢ(a), qᵢ(b))` of the new edge of `G_i`
    -- (`lem:case-III-chain-eq666`):
    (hρe₀ : ρ₀ (panelSupportExtensor
          (fun j => (fun p => q (cd.shiftPerm i.castSucc p.1, p.2)) (cd.vtx i.succ, j))
          (fun j => (fun p => q (cd.shiftPerm i.castSucc p.1, p.2))
            (cd.vtx (⟨(i : ℕ) - 1, by have := i.isLt; omega⟩ : Fin cd.d).castSucc, j))) = 0)
    -- `hingeRow a b (−ρ₀)` lies in the row space of `R(G − vᵢ, qᵢ)` with the selector `ends₀`
    -- (`lem:case-III-chain-eq666`):
    (hρGv : BodyHingeFramework.hingeRow (cd.vtx i.succ)
        (cd.vtx (⟨(i : ℕ) - 1, by have := i.isLt; omega⟩ : Fin cd.d).castSucc) (-ρ₀)
      ∈ Submodule.span K (PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx i.castSucc))
        ends₀
        (fun p => q (cd.shiftPerm i.castSucc p.1, p.2))).toBodyHinge.rigidityRows)
    -- `ends₀` gives each link of `G_1`, split off at `v₁` along `v₂v₀`, its ends in some order, for
    -- `candidateEnds_records_splitOff_isLink`:
    (hrec' : ∀ f x y, (G.splitOff (cd.vtx (⟨1, by have := i.isLt; omega⟩ : Fin cd.d).castSucc)
        (cd.vtx (⟨1, by have := i.isLt; omega⟩ : Fin cd.d).succ)
        (cd.vtx (⟨0, by have := i.isLt; omega⟩ : Fin cd.d).castSucc) cd.e₀).IsLink f x y →
      ends₀ f = (x, y) ∨ ends₀ f = (y, x))
    -- the bottom rows, each a row of `R(G − vᵢ, qᵢ)` with the selector `cd.candidateEnds i ends₀`,
    -- at which `chainData_bottom_relabel` gives them, or a form `hingeRow a b ρ'` with `ρ'`
    -- vanishing on `C(qᵢ(a), qᵢ(b))`:
    {ιb : Type*} [Finite ιb] {w : ιb → Module.Dual K (α → ScrewSpace K k)}
    (hwcard : Nat.card ιb = screwDim k * (V(G).ncard - 2))
    (hw : LinearIndependent K w)
    (hwmem : ∀ j, w j ∈ (PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx i.castSucc))
        (cd.candidateEnds i ends₀)
        (fun p => q (cd.shiftPerm i.castSucc p.1, p.2))).toBodyHinge.rigidityRows ∨
      ∃ ρ' : Module.Dual K (ScrewSpace K k),
        ρ' (panelSupportExtensor
            (fun j => (fun p => q (cd.shiftPerm i.castSucc p.1, p.2)) (cd.vtx i.succ, j))
            (fun j => (fun p => q (cd.shiftPerm i.castSucc p.1, p.2))
              (cd.vtx (⟨(i : ℕ) - 1, by have := i.isLt; omega⟩ : Fin cd.d).castSucc, j))) = 0 ∧
        w j = BodyHingeFramework.hingeRow (cd.vtx i.succ)
          (cd.vtx (⟨(i : ℕ) - 1, by have := i.isLt; omega⟩ : Fin cd.d).castSucc) ρ')
    (hdef : G.deficiency n = 0) :
    PanelHingeFramework.HasGenericFullRankRealization K k n G := by
  classical
  have : Fintype α := Fintype.ofFinite α
  have h0i : 0 < (i : ℕ) := by omega
  -- The split `(v, a, b, e_a, e_b)` at the interior vertex `vtx i.castSucc`, from `cd`.
  set v := cd.vtx i.castSucc with hv
  set a := cd.vtx i.succ with ha
  set b := cd.vtx (⟨(i : ℕ) - 1, by omega⟩ : Fin cd.d).castSucc with hb
  set e_a := cd.edge i with hea
  set e_b := cd.edge ⟨(i : ℕ) - 1, by omega⟩ with heb
  -- The normals `qρ = q ∘ σᵢ`.
  set qρ : α × Fin (k + 2) → K := fun p => q (cd.shiftPerm i.castSucc p.1, p.2) with hqρ
  set Gv := G.removeVertex v with hGv
  -- `qρ(a) = q(a)` and `qρ(b) = q(v)`.
  have hqρa : (fun j => qρ (a, j)) = (fun j => q (a, j)) := cd.seedShift_succ_castSucc i q
  have hqρb : (fun j => qρ (b, j)) = (fun j => q (v, j)) := cd.seedShift_pred_castSucc h2i q
  -- The two edges of the chain at `v`, from `v`.
  have hlea : G.IsLink e_a v a := cd.isLink_succ_edge i
  have hleb : G.IsLink e_b v b := cd.isLink_pred_edge h0i
  -- Distinctness of the tuple, from `vtx_inj`/`edge_inj`.
  have heab : e_a ≠ e_b := (cd.pred_edge_ne h0i).symm
  have hvG : v ∈ V(G) := cd.vtx_mem _
  -- Facts on `Gv` and `G`, from `cd`.
  have hvVc : v ∉ V(Gv) := cd.notMem_vertexSet_removeVertex_castSucc i
  have haVc : a ∈ V(Gv) := cd.succ_mem_vertexSet_removeVertex_castSucc i
  have hbVc : b ∈ V(Gv) := cd.pred_castSucc_mem_vertexSet_removeVertex_castSucc h0i
  have hleG : ∀ e u w, Gv.IsLink e u w → G.IsLink e u w :=
    fun e u w hlink => (Graph.removeVertex_isLink.mp hlink).1
  have hsplitG : ∀ e u w, G.IsLink e u w → e = e_a ∨ e = e_b ∨ Gv.IsLink e u w :=
    fun e u w hlink => cd.isLink_eq_succ_or_pred_or_removeVertex h0i hlink
  have hcard_Gv : V(Gv).ncard = V(G).ncard - 1 := by
    rw [hGv, Graph.vertexSet_removeVertex, Set.ncard_sdiff_singleton_of_mem hvG]
  have hVone : 1 ≤ V(Gv).ncard := (Set.ncard_pos (Set.toFinite _)).mpr ⟨a, haVc⟩
  have hVcard : V(G).ncard = V(Gv).ncard + 1 := by rw [hcard_Gv]; omega
  -- The two edges at `v` are not links of `Gv` (`v ∉ V(Gv)`), so on the links of `Gv` `endsσρ₁`
  -- agrees with `ends₀`.
  have hGv_off : ∀ {e u w}, Gv.IsLink e u w → e ≠ e_a ∧ e ≠ e_b := fun hlink =>
    ⟨hlea.ne_of_notMem hvVc hleG hlink, hleb.ne_of_notMem hvVc hleG hlink⟩
  -- The rows of `R(Gv, qρ)` with `ends₀`, at which `hρGv` is stated, and with `endsσρ₁` are the
  -- same, as the two selectors agree on the links of `Gv` (`rigidityRows_ofNormals_congr_ends`).
  have hcongr : (PanelHingeFramework.ofNormals Gv ends₀ qρ).toBodyHinge.rigidityRows
      = (PanelHingeFramework.ofNormals Gv endsσρ₁ qρ).toBodyHinge.rigidityRows :=
    PanelHingeFramework.rigidityRows_ofNormals_congr_ends qρ
      (fun e u w hlink => (hoff e (hGv_off hlink).1 (hGv_off hlink).2).symm)
  -- The rows with `candidateEnds i ends₀`, at which `hwmem` is stated, and with `endsσρ₁` are the
  -- same, as both give each link of `Gv` its ends in some order
  -- (`rigidityRows_ofNormals_congr_ends_swap`).
  have hcongr_swap :
      (PanelHingeFramework.ofNormals Gv (cd.candidateEnds i ends₀) qρ).toBodyHinge.rigidityRows
        = (PanelHingeFramework.ofNormals Gv endsσρ₁ qρ).toBodyHinge.rigidityRows :=
    PanelHingeFramework.rigidityRows_ofNormals_congr_ends_swap qρ <| by
      intro e u w hlink
      -- The link `e u w` of `Gv` is a link of `G.splitOff v a b cd.e₀` (`u, w ≠ v`, and `e ≠ e₀` as
      -- `e₀ ∉ E(G)`), so `candidateEnds i ends₀` gives it its ends
      -- (`candidateEnds_records_splitOff_isLink`).
      obtain ⟨hGlink, hunev, hwnev⟩ := Graph.removeVertex_isLink.mp hlink
      have hsplit : (G.splitOff v a b cd.e₀).IsLink e u w :=
        Graph.splitOff_isLink.mpr
          (Or.inl ⟨fun he => cd.e₀_fresh (he ▸ hGlink.edge_mem), hGlink, hunev, hwnev⟩)
      refine ⟨cd.candidateEnds_records_splitOff_isLink i (by omega) hrec' hsplit, ?_⟩
      -- `endsσρ₁` gives the link of `Gv` its ends in some order (`hends_Gv` gives
      -- `Gv.IsLink e (endsσρ₁ e).1 (endsσρ₁ e).2`; compare with the link by
      -- `eq_and_eq_or_eq_and_eq`).
      rcases hlink.eq_and_eq_or_eq_and_eq (hends_Gv e u w hlink) with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl (Prod.ext h1.symm h2.symm)
      · exact Or.inr (Prod.ext h2.symm h1.symm)
  -- `hρGv` passes to `endsσρ₁` through `hcongr`, and the bottom rows through `hcongr_swap`.
  have hρGv₁ : BodyHingeFramework.hingeRow a b (-ρ₀) ∈ Submodule.span K
      (PanelHingeFramework.ofNormals Gv endsσρ₁ qρ).toBodyHinge.rigidityRows := by
    rw [← hcongr]; exact hρGv
  have hwmem₁ : ∀ j, w j ∈ (PanelHingeFramework.ofNormals Gv endsσρ₁ qρ).toBodyHinge.rigidityRows ∨
      ∃ ρ' : Module.Dual K (ScrewSpace K k),
        ρ' (panelSupportExtensor (fun j => qρ (a, j)) (fun j => qρ (b, j))) = 0 ∧
        w j = BodyHingeFramework.hingeRow a b ρ' := by
    intro j
    rcases hwmem j with hgen | hcand
    · exact Or.inl (by rw [← hcongr_swap]; exact hgen)
    · exact Or.inr hcand
  -- The realization, by `case_III_arm_realization` at `qρ` and `-ρ₀`.
  refine PanelHingeFramework.case_III_arm_realization (k := k) G Gv endsσρ₁ (q := qρ)
    (v := v) (a := a) (b := b) (e_a := e_a) (e_b := e_b) (n' := n')
    hvVc haVc hbVc hlea hleb hends_ea hends_eb heab hleG hsplitG hends_Gv hne_Gv
    hVone hVcard ?hLn ?hgab (ρ := -ρ₀) ?hρgate ?hρe₀ ?hρGv (ιb := ιb) (w := w)
    ?hwcard hw ?hwmem hdef
  case hLn => rw [hqρa]; exact hLn
  case hgab => rw [hqρa, hqρb]; exact hgab
  case hρgate =>
    rw [hqρa, LinearMap.neg_apply, neg_ne_zero]; exact hρgate
  case hρe₀ =>
    -- the hinge `C(qρ a, qρ b)` is that of `hρe₀` by definition; the sign of `-ρ₀`.
    rw [LinearMap.neg_apply, neg_eq_zero]; exact hρe₀
  case hρGv =>
    -- `hingeRow a b (-ρ₀) ∈ span (ofNormals Gv endsσρ₁ qρ).rigidityRows`, from `hρGv` through
    -- `hcongr`.
    exact hρGv₁
  case hwcard => rw [hwcard, hcard_Gv, Nat.sub_sub]
  case hwmem => exact hwmem₁

/-! ## The choice of a panel (`lem:case-III-chain-discriminator`) -/

/-- **The choice of a panel** (a step of `lem:case-III-chain-discriminator`; KT eq. (6.67) and the
proof of KT eq. (6.65), p. 698): if the `k + 1` normals `q(cand i, ·)` are linearly independent and
`ρ ≠ 0` is a linear form on `K^D`, there are `u : Fin (k + 1)` and a normal `n'`, linearly
independent of `q(cand u, ·)`, with `ρ(C(q(cand u, ·), n')) ≠ 0`. This is KT Claim 6.12 in the form
for every `d` (the note after `lem:case-III-claim612`), for the panels of `cand 0, …, cand k`.

The proof, as in the proof of `lem:case-III-chain-discriminator`.
`exists_homogeneousIncidence_of_normals_gen`
(`lem:case-III-claim612-points-affineIndep-real-normals`) gives `k + 2` linearly independent vectors
`pbar`, the first orthogonal to every normal and each other orthogonal to all of them but one: Katoh
and Tanigawa's points `p_d` and `p_l` (KT p. 698), in homogeneous coordinates.
`BodyHingeFramework.exists_complementIso_ne_zero_of_homogeneousIncidence_gen` gives `u`, `n'` and
`ρ(complementIso ⟨extensor ![q(cand u, ·), n'], _⟩) ≠ 0`, which
`panelSupportExtensor_eq_complementIso_extensor` rewrites as `ρ(C(q(cand u, ·), n')) ≠ 0`. -/
theorem PanelHingeFramework.exists_chainData_discriminator_pick_of_LI {k : ℕ}
    {α : Type*} {q : α × Fin (k + 2) → K}
    {cand : Fin (k + 1) → α}
    (hn : LinearIndependent K (fun (i : Fin (k + 1)) (j : Fin (k + 2)) => q (cand i, j)))
    {ρ : Module.Dual K (ScrewSpace K k)} (hρ : ρ ≠ 0) :
    ∃ (u : Fin (k + 1)) (n' : Fin (k + 2) → K),
      LinearIndependent K ![fun j => q (cand u, j), n'] ∧
      ρ (panelSupportExtensor (fun j => q (cand u, j)) n') ≠ 0 := by
  -- The `k + 2` vectors with the incidences of Katoh and Tanigawa's points (KT p. 698).
  obtain ⟨pbar, hp, h0, hi⟩ := exists_homogeneousIncidence_of_normals_gen hn
  -- KT Claim 6.12 for every `d`: `u`, `n'`, and `ρ` not vanishing on the meet form.
  obtain ⟨u, n', hpair, hgate⟩ :=
    BodyHingeFramework.exists_complementIso_ne_zero_of_homogeneousIncidence_gen hρ hp hn h0
      (fun i j hji => (hi i).1 j hji)
  -- The meet form as a `panelSupportExtensor`.
  exact ⟨u, n', hpair, by rwa [panelSupportExtensor_eq_complementIso_extensor]⟩

/-- **The form `r` and the choice of a panel at a split** (a step of
`lem:case-III-chain-discriminator`): under the hypotheses of `chainData_split_w6b_gates` for a split
`(v, a, b)` with the new edge `cd.e₀`, there are the normals `q`, the selector `ends`, the form
`ρ₀`, the bottom rows `w`, the forms `rab` and the combination of its conclusion, and moreover an
index `i : Fin cd.d` and a normal `n'`, linearly independent of `q(u_i)`, with
`ρ₀(C(q(u_i), n')) ≠ 0`, where `u_i = cd.candidateVtx i` (KT eq. (6.67), p. 698).
`chainData_fire_discriminator` applies it at the split at `v₁` along `v₀v₂`.

The proof, as in the proof of `lem:case-III-chain-discriminator`. The polynomial of
`exists_tupleLI_polynomial` for the distinct `u_0, …, u_{d−1}` (`Graph.ChainData.candidatePanel`,
`Graph.ChainData.candidatePanel_injective`) is the fourth factor: `chainData_split_w6b_gates`, with
it as `Pu`, gives normals off its zeros, at which the normals of the `d` panels are linearly
independent. Then `exists_chainData_discriminator_pick_of_LI` chooses the panel `u`, and `i` is `u`
cast to `Fin cd.d` (`Graph.ChainData.d_eq_kAdd`, `Graph.ChainData.candidatePanel_apply`). -/
theorem PanelHingeFramework.exists_shared_redundancy_and_matched_candidate [Infinite K]
    [Finite α] [Finite β]
    {G : Graph α β} {n : ℕ} (cd : G.ChainData n) (hk1 : 1 ≤ k)
    (hn : Graph.bodyBarDim n = screwDim k)
    (v a b : α) (hav : a ≠ v) (hbv : b ≠ v) (hba : b ≠ a)
    (haG : a ∈ V(G)) (hbG : b ∈ V(G)) (he₀ : cd.e₀ ∉ E(G)) (hGloop : G.Loopless)
    (h622lb : ∀ (ends : β → α × α),
      (∀ e u w, (G.splitOff v a b cd.e₀).IsLink e u w → ends e = (u, w) ∨ ends e = (w, u)) →
      ∃ P : MvPolynomial (α × Fin (k + 2)) K, P ≠ 0 ∧
        ∀ q : α × Fin (k + 2) → K, MvPolynomial.eval q P ≠ 0 →
          screwDim k * (V(G.splitOff v a b cd.e₀).ncard - 1) - (screwDim k - 2)
            ≤ Module.finrank K (Submodule.span K
                (PanelHingeFramework.ofNormals (G.removeVertex v) ends
                  q).toBodyHinge.rigidityRows))
    (hdef_Gab : (G.splitOff v a b cd.e₀).deficiency n = 0)
    (hsplitGP : PanelHingeFramework.HasGenericFullRankRealization K k n (G.splitOff v a b cd.e₀)) :
    ∃ (q : α × Fin (k + 2) → K) (ends : β → α × α)
      (ρ₀ : Module.Dual K (ScrewSpace K k))
      (w : Fin (screwDim k * (V(G.splitOff v a b cd.e₀).ncard - 1)) →
        Module.Dual K (α → ScrewSpace K k))
      (lamAB : Fin (screwDim k - 1) → K)
      (rab : Fin (screwDim k - 1) → Module.Dual K (ScrewSpace K k))
      (i : Fin cd.d) (n' : Fin (k + 2) → K),
      -- `ofNormals Gab ends q` is in general position, and `ends` records the links of `Gab`
      (PanelHingeFramework.ofNormals (G.splitOff v a b cd.e₀) ends q).IsGeneralPosition ∧
      PanelHingeFramework.RecordsLinks (G.splitOff v a b cd.e₀) ends ∧
      -- the form `ρ₀`, nonzero, vanishing on `C(q(a), q(b))`
      ρ₀ ≠ 0 ∧
      ρ₀ (panelSupportExtensor (fun j => q (a, j)) (fun j => q (b, j))) = 0 ∧
      -- the bottom rows, and `ρ₀ = ∑_j lamAB j • rab j` with each `rab j` in the hinge-row block of
      -- `e₀`
      LinearIndependent K w ∧
      (∀ j, w j ∈
          (PanelHingeFramework.ofNormals (G.removeVertex v) ends q).toBodyHinge.rigidityRows ∨
        ∃ ρ' : Module.Dual K (ScrewSpace K k),
          ρ' (panelSupportExtensor (fun j => q (a, j)) (fun j => q (b, j))) = 0 ∧
          w j = BodyHingeFramework.hingeRow a b ρ') ∧
      (∀ j, rab j ∈ BodyHingeFramework.hingeRowBlock
        (PanelHingeFramework.ofNormals (G.splitOff v a b cd.e₀) ends q).toBodyHinge cd.e₀) ∧
      ρ₀ = ∑ j, lamAB j • rab j ∧
      -- `hingeRow a b ρ₀` as a combination of rows of `R(G − v, q)` grouped by edge, which the
      -- proof of `lem:case-III-chain-dispatch` reads at the edge `v_i v_{i+1}` (KT eq. (6.66))
      (∃ (nGv : ℕ) (cGv : Fin nGv → K) (evGv : Fin nGv → β) (uvGv vvGv : Fin nGv → α)
          (rvGv : Fin nGv → Module.Dual K (ScrewSpace K k)),
        (∀ j, (G.removeVertex v).IsLink (evGv j) (uvGv j) (vvGv j)) ∧
        (∀ j, rvGv j ∈ ((PanelHingeFramework.ofNormals (G.removeVertex v) ends q).toBodyHinge
          ).hingeRowBlock (evGv j)) ∧
        BodyHingeFramework.hingeRow a b ρ₀
          = ∑ j, cGv j • BodyHingeFramework.hingeRow (uvGv j) (vvGv j) (rvGv j)) ∧
      -- the chosen panel, of `u_i = candidateVtx i`, and the normal `n'`
      LinearIndependent K ![fun j => q (cd.candidateVtx i, j), n'] ∧
      ρ₀ (panelSupportExtensor (fun j => q (cd.candidateVtx i, j)) n') ≠ 0 ∧
      -- `hingeRow a b ρ₀` lies in the row space of `R(G − v, q)` with the selector `ends`
      BodyHingeFramework.hingeRow a b ρ₀ ∈ Submodule.span K
        (PanelHingeFramework.ofNormals (G.removeVertex v) ends q).toBodyHinge.rigidityRows := by
  -- The polynomial that makes `q(u_0), …, q(u_{d−1})` linearly independent, for the injective
  -- `candidatePanel hn`: the `Pu` of `chainData_split_w6b_gates`.
  obtain ⟨Ptup, hPtup_ne, hPtup_trans⟩ :=
    exists_tupleLI_polynomial (K := K) (cd.candidatePanel_injective hn)
  -- The normals, off the zeros of `Ptup`, the form `ρ₀`, the bottom rows and the forms `rab`.
  obtain ⟨q, ends, ρ₀, w, lamAB, rab, hgp, hends', hρ₀ne, hρ₀e₀, hρ₀Gv, hw,
      hwmem, hrab_blk, hρ₀_lam, hedgeGv, hPtup_eval⟩ :=
    PanelHingeFramework.chainData_split_w6b_gates hk1 G v a b cd.e₀ hav hbv hba haG hbG
      he₀ hGloop Ptup hPtup_ne h622lb hn hdef_Gab hsplitGP
  -- The choice of a panel, at `ρ₀` and at the normals `q`, whose panels are linearly independent by
  -- `Ptup`.
  obtain ⟨u, n', hLI, hgate⟩ :=
    PanelHingeFramework.exists_chainData_discriminator_pick_of_LI
      (hPtup_trans q hPtup_eval) hρ₀ne
  -- The index `i := Fin.cast d_eq_kAdd.symm u`; `candidatePanel hn u` is `candidateVtx i` by
  -- definition (`candidatePanel_apply`).
  refine ⟨q, ends, ρ₀, w, lamAB, rab, Fin.cast (cd.d_eq_kAdd hn).symm u, n', hgp, hends',
    hρ₀ne, hρ₀e₀, hw, hwmem, hrab_blk, hρ₀_lam, hedgeGv, ?_, ?_, hρ₀Gv⟩
  · rw [← cd.candidatePanel_apply hn u]; exact hLI
  · rw [← cd.candidatePanel_apply hn u]; exact hgate

/-- **The form `r` and the choice of a panel** (`lem:case-III-chain-discriminator`; KT
eqs. (6.65)–(6.67), pp. 697–698): let `K` be infinite, `D = bodyBarDim n = screwDim k` with `1 ≤ k`,
`G` a simple minimal `0`-dof-graph with `|V(G)| ≥ 3`, and `cd` a chain of length `d ≥ 2` in `G`
(`hd2`). Suppose that `hIH` holds, as in `exists_nested_rankPolynomial_lower_all_k`, and that
`G_1 = G.splitOff v₁ v₀ v₂ e₀` has deficiency `0` and a generic full-rank realization. Then there
are normals `q`, a selector `ends` that gives each link of `G_1` its ends in some order, with
`ofNormals G_1 ends q` in general position, a nonzero linear form `ρ₀` on `K^D` with
`ρ₀(C(q(v₀), q(v₂))) = 0`, whose row `hingeRow v₀ v₂ ρ₀` lies in the row space of `R(G − v₁, q)`,
`D(|V(G_1)| − 1)` linearly independent forms `w`, each a row of `R(G − v₁, q)` or a form
`hingeRow v₀ v₂ ρ'` with `ρ'` vanishing on `C(q(v₀), q(v₂))`, and an index `i : Fin cd.d` and a
normal `n'`, linearly independent of `q(u_i)`, with `ρ₀(C(q(u_i), n')) ≠ 0`, where
`u_i = cd.candidateVtx i`. Moreover, `ρ₀ = ∑_j lamAB j • rab j` with the `rab j` in the hinge-row
block of `e₀`, and `hingeRow v₀ v₂ ρ₀` is a combination of rows of `R(G − v₁, q)` grouped by edge.
`chainData_dispatch` (`lem:case-III-chain-dispatch`) uses all of this but the forms `rab`.

The proof, as in the proof of `lem:case-III-chain-discriminator`. As `d ≥ 2`, `v₁` is interior: its
edges are `edge 0` to `v₀` and `edge 1` to `v₂` (`Graph.ChainData.splitOff_data_one`).
`exists_nested_rankPolynomial_lower_all_k` (`lem:case-III-nested-rank-lower`) gives the bound of KT
eq. (6.22) at `G − v₁`, and `exists_shared_redundancy_and_matched_candidate`, at the split
`(v₁, v₀, v₂)`, the rest. -/
theorem PanelHingeFramework.chainData_fire_discriminator [Infinite K]
    [DecidableEq β] [Finite α] [Finite β]
    {G : Graph α β} {n : ℕ} (cd : G.ChainData n) (hd2 : 2 ≤ cd.d) (hk1 : 1 ≤ k)
    (hn : Graph.bodyBarDim n = screwDim k)
    (hG : G.IsMinimalKDof n 0) (hV3 : 3 ≤ V(G).ncard) (hSimple : G.Simple)
    (hIH : ∀ (k' : ℤ) (G' : Graph α β), G'.IsMinimalKDof n k' → V(G').Nonempty →
      V(G').ncard < V(G).ncard →
      (G'.Simple → PanelHingeFramework.HasGenericFullRankRealization K k n G') ∧
        HasPanelRealization K k n G')
    (hdef_Gab : (G.splitOff (cd.vtx ⟨1, by omega⟩) (cd.vtx ⟨0, by omega⟩)
      (cd.vtx ⟨2, by omega⟩) cd.e₀).deficiency n = 0)
    (hsplitGP : PanelHingeFramework.HasGenericFullRankRealization K k n
      (G.splitOff (cd.vtx ⟨1, by omega⟩) (cd.vtx ⟨0, by omega⟩) (cd.vtx ⟨2, by omega⟩) cd.e₀)) :
    ∃ (q : α × Fin (k + 2) → K) (ends : β → α × α)
      (ρ₀ : Module.Dual K (ScrewSpace K k))
      (w : Fin (screwDim k * (V(G.splitOff (cd.vtx ⟨1, by omega⟩) (cd.vtx ⟨0, by omega⟩)
          (cd.vtx ⟨2, by omega⟩) cd.e₀).ncard - 1)) → Module.Dual K (α → ScrewSpace K k))
      (lamAB : Fin (screwDim k - 1) → K)
      (rab : Fin (screwDim k - 1) → Module.Dual K (ScrewSpace K k))
      (i : Fin cd.d) (n' : Fin (k + 2) → K),
      (PanelHingeFramework.ofNormals (G.splitOff (cd.vtx ⟨1, by omega⟩) (cd.vtx ⟨0, by omega⟩)
        (cd.vtx ⟨2, by omega⟩) cd.e₀) ends q).IsGeneralPosition ∧
      PanelHingeFramework.RecordsLinks (G.splitOff (cd.vtx ⟨1, by omega⟩) (cd.vtx ⟨0, by omega⟩)
        (cd.vtx ⟨2, by omega⟩) cd.e₀) ends ∧
      ρ₀ ≠ 0 ∧
      ρ₀ (panelSupportExtensor (fun j => q (cd.vtx ⟨0, by omega⟩, j))
        (fun j => q (cd.vtx ⟨2, by omega⟩, j))) = 0 ∧
      LinearIndependent K w ∧
      (∀ j, w j ∈ (PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx ⟨1, by omega⟩))
          ends q).toBodyHinge.rigidityRows ∨
        ∃ ρ' : Module.Dual K (ScrewSpace K k),
          ρ' (panelSupportExtensor (fun j => q (cd.vtx ⟨0, by omega⟩, j))
            (fun j => q (cd.vtx ⟨2, by omega⟩, j))) = 0 ∧
          w j = BodyHingeFramework.hingeRow (cd.vtx ⟨0, by omega⟩) (cd.vtx ⟨2, by omega⟩) ρ') ∧
      (∀ j, rab j ∈ BodyHingeFramework.hingeRowBlock
        (PanelHingeFramework.ofNormals (G.splitOff (cd.vtx ⟨1, by omega⟩) (cd.vtx ⟨0, by omega⟩)
          (cd.vtx ⟨2, by omega⟩) cd.e₀) ends q).toBodyHinge cd.e₀) ∧
      ρ₀ = ∑ j, lamAB j • rab j ∧
      (∃ (nGv : ℕ) (cGv : Fin nGv → K) (evGv : Fin nGv → β) (uvGv vvGv : Fin nGv → α)
          (rvGv : Fin nGv → Module.Dual K (ScrewSpace K k)),
        (∀ j, (G.removeVertex (cd.vtx ⟨1, by omega⟩)).IsLink (evGv j) (uvGv j) (vvGv j)) ∧
        (∀ j, rvGv j ∈ ((PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx ⟨1, by omega⟩))
          ends q).toBodyHinge).hingeRowBlock (evGv j)) ∧
        BodyHingeFramework.hingeRow (cd.vtx ⟨0, by omega⟩) (cd.vtx ⟨2, by omega⟩) ρ₀
          = ∑ j, cGv j • BodyHingeFramework.hingeRow (uvGv j) (vvGv j) (rvGv j)) ∧
      LinearIndependent K ![fun j => q (cd.candidateVtx i, j), n'] ∧
      ρ₀ (panelSupportExtensor (fun j => q (cd.candidateVtx i, j)) n') ≠ 0 ∧
      BodyHingeFramework.hingeRow (cd.vtx ⟨0, by omega⟩) (cd.vtx ⟨2, by omega⟩) ρ₀ ∈
        Submodule.span K (PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx ⟨1, by omega⟩))
          ends q).toBodyHinge.rigidityRows := by
  -- The split `(v, a, b) = (vtx 1, vtx 0, vtx 2)`, with the edges `edge 0 : v₀v₁` and
  -- `edge 1 : v₁v₂` from `v₁`, and the edges of `G` at `v₁` (`Graph.ChainData.splitOff_data_one`).
  obtain ⟨hav, hbv, hba, heab, hlea, hleb, hclv⟩ := cd.splitOff_data_one hd2
  -- The bound of KT eq. (6.22) at `G − v₁` off the zeros of a polynomial.
  have h622lb := PanelHingeFramework.exists_nested_rankPolynomial_lower_all_k hk1 hn G
    (cd.vtx ⟨1, by omega⟩) (cd.vtx ⟨0, by omega⟩) (cd.vtx ⟨2, by omega⟩)
    (cd.edge ⟨0, by omega⟩) (cd.edge ⟨1, by omega⟩) cd.e₀ hG hV3 hSimple hba hav hbv heab
    hlea hleb hclv cd.e₀_fresh hIH
  -- The form and the choice of a panel at the split.
  exact PanelHingeFramework.exists_shared_redundancy_and_matched_candidate cd hk1 hn
    (cd.vtx ⟨1, by omega⟩) (cd.vtx ⟨0, by omega⟩) (cd.vtx ⟨2, by omega⟩) hav hbv hba
    (cd.vtx_mem _) (cd.vtx_mem _) cd.e₀_fresh hSimple.toLoopless h622lb hdef_Gab hsplitGP

/-! ## Case III for a chain (`lem:case-III-chain-dispatch`)

From the choice of the panel of `u_i` (`chainData_fire_discriminator`), Katoh and Tanigawa's
framework `(G, p_i)`: for `2 ≤ i` from `(G_i, q_i)` (`chainData_dispatch_interior_of_discriminator`,
`chainData_dispatch_interior`), and for `i ≤ 1` at the split at `v₁`
(`chainData_dispatch_floor_of_discriminator`). -/

/-- **The framework `(G, p_i)` for `2 ≤ i`, from a selector that gives every edge its ends** (a step
of `lem:case-III-chain-dispatch`): let `cd` be a chain of length `d ≥ 3` in a simple `G` of
deficiency `0`, `2 ≤ i`, `q` normals any two of which are linearly independent, and `ends₀` a
selector that gives each link of `G` its ends in some order (`hrec_G`) and `e₀` the ends `(v₂, v₀)`.
Let `ρ₀`, the bottom rows `w` and the combination be as `chainData_fire_discriminator` gives them,
at the selector `ends₀`, with `D(|V(G)| − 2)` rows `w`, and let `n'`, linearly independent of
`q(u_i)`, satisfy `ρ₀(C(q(u_i), n')) ≠ 0`. Then `G` has a generic full-rank realization.

The proof, as in the proof of `lem:case-III-chain-dispatch` for `2 ≤ i`. With `σᵢ` and
`qᵢ = q ∘ σᵢ`, `Graph.ChainData.interior_hρe₀_of_baseWidening` and
`Graph.ChainData.chainData_relabel_arm_hρGv` (`lem:case-III-chain-eq666`, KT eq. (6.66)) give that
`ρ₀` vanishes on the hinge of the new edge `vᵢ₋₁vᵢ₊₁` of `(G_i, q_i)` and that
`hingeRow vᵢ₊₁ vᵢ₋₁ (−ρ₀)` lies in the row space of `R(G − vᵢ, qᵢ)`, and `chainData_bottom_relabel`
(`lem:case-III-chain-relabel-rows`) renames the bottom rows along `σᵢ`, which keeps them linearly
independent (the rows of the new edge taken at the orientation `(v₂, v₀)`, with `−ρ'` for `ρ'`). As
`u_i = vᵢ₊₁` (`Graph.ChainData.candidateVtx_succ_eq`), `chainData_interior_realization_hρGv` gives
the realization, with the selector `ends₀` given the ends `(vᵢ, vᵢ₊₁)` and `(vᵢ, vᵢ₋₁)` at the two
edges at `vᵢ`. -/
theorem PanelHingeFramework.chainData_dispatch_interior [Infinite K]
    [Finite α] [Finite β]
    {G : Graph α β} {n : ℕ} (cd : G.ChainData n) (h3 : 3 ≤ cd.d) (hSimple : G.Simple)
    (i : Fin cd.d) (h2i : 2 ≤ (i : ℕ))
    {q : α × Fin (k + 2) → K} {ends₀ : β → α × α}
    {ρ₀ : Module.Dual K (ScrewSpace K k)}
    {ιb : Type*} [Finite ιb] {w : ιb → Module.Dual K (α → ScrewSpace K k)}
    (hwcard : Nat.card ιb = screwDim k * (V(G).ncard - 2))
    {n' : Fin (k + 2) → K}
    (hgp_seed : ∀ x y : α, x ≠ y → LinearIndependent K ![fun j => q (x, j), fun j => q (y, j)])
    (hrec_G : ∀ f x y, G.IsLink f x y → ends₀ f = (x, y) ∨ ends₀ f = (y, x))
    (he₀rec : ends₀ cd.e₀ = (cd.vtx ⟨2, by omega⟩, cd.vtx ⟨0, by omega⟩))
    (hρ₀e₀ : ρ₀ (panelSupportExtensor (fun j => q (cd.vtx ⟨0, by omega⟩, j))
      (fun j => q (cd.vtx ⟨2, by omega⟩, j))) = 0)
    (hw : LinearIndependent K w)
    (hwmem' : ∀ j, w j ∈ (PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx ⟨1, by omega⟩))
        ends₀ q).toBodyHinge.rigidityRows ∨
      ∃ ρ' : Module.Dual K (ScrewSpace K k),
        ρ' (panelSupportExtensor (fun j => q (cd.vtx ⟨0, by omega⟩, j))
          (fun j => q (cd.vtx ⟨2, by omega⟩, j))) = 0 ∧
        w j = BodyHingeFramework.hingeRow (cd.vtx ⟨0, by omega⟩) (cd.vtx ⟨2, by omega⟩) ρ')
    (hedgeGv :
      ∃ (nGv : ℕ) (cGv : Fin nGv → K) (evGv : Fin nGv → β) (uvGv vvGv : Fin nGv → α)
          (rvGv : Fin nGv → Module.Dual K (ScrewSpace K k)),
        (∀ j, (G.removeVertex (cd.vtx ⟨1, by omega⟩)).IsLink (evGv j) (uvGv j) (vvGv j)) ∧
        (∀ j, rvGv j ∈ (PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx ⟨1, by omega⟩))
          ends₀ q).toBodyHinge.hingeRowBlock (evGv j)) ∧
        BodyHingeFramework.hingeRow (cd.vtx ⟨0, by omega⟩) (cd.vtx ⟨2, by omega⟩) ρ₀
          = ∑ j, cGv j • BodyHingeFramework.hingeRow (uvGv j) (vvGv j) (rvGv j))
    (hLI : LinearIndependent K ![fun j => q (cd.candidateVtx i, j), n'])
    (hgate : ρ₀ (panelSupportExtensor (fun j => q (cd.candidateVtx i, j)) n') ≠ 0)
    (hρ₀Gv : BodyHingeFramework.hingeRow (cd.vtx ⟨0, by omega⟩) (cd.vtx ⟨2, by omega⟩) ρ₀ ∈
      Submodule.span K (PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx ⟨1, by omega⟩))
        ends₀ q).toBodyHinge.rigidityRows)
    (hdef : G.deficiency n = 0) :
    PanelHingeFramework.HasGenericFullRankRealization K k n G := by
  classical
  have : Fintype α := Fintype.ofFinite α
  have h0i : 0 < (i : ℕ) := by omega
  have hid : (i : ℕ) < cd.d := i.isLt
  -- The split `(v, a, b, e_a, e_b)` at `vtx i.castSucc`, and the normals `qρ = q ∘ σᵢ`.
  set v := cd.vtx i.castSucc with hv
  set a := cd.vtx i.succ with ha
  set b := cd.vtx (⟨(i : ℕ) - 1, by omega⟩ : Fin cd.d).castSucc with hb
  set e_a := cd.edge i with hea
  set e_b := cd.edge ⟨(i : ℕ) - 1, by omega⟩ with heb
  set qρ : α × Fin (k + 2) → K := fun p => q (cd.shiftPerm i.castSucc p.1, p.2) with hqρ
  set Gv := G.removeVertex v with hGv
  have hGloop : G.Loopless := hSimple.toLoopless
  have : Gv.Loopless := hGloop.mono (hGv ▸ Graph.removeVertex_le G v)
  -- The two edges at `v`, from `v`, and their distinctness.
  have hlea : G.IsLink e_a v a := cd.isLink_succ_edge i
  have hleb : G.IsLink e_b v b := cd.isLink_pred_edge h0i
  have heab : e_a ≠ e_b := (cd.pred_edge_ne h0i).symm
  -- `ends₀` gives `e₀` the ends `v₀` and `v₂` in some order.
  have hrece₀ : ends₀ cd.e₀ = (cd.vtx ⟨0, by omega⟩, cd.vtx ⟨2, by omega⟩) ∨
      ends₀ cd.e₀ = (cd.vtx ⟨2, by omega⟩, cd.vtx ⟨0, by omega⟩) := Or.inr he₀rec
  -- (1) `ρ₀` vanishes on the hinge of `e₀` in `ofNormals (G − v₁) ends₀ q`: by `he₀rec` it is
  -- `C(q(v₂), q(v₀)) = -C(q(v₀), q(v₂))` (`panelSupportExtensor_swap`).
  have hρe₀base : ρ₀ ((PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx ⟨1, by omega⟩))
      ends₀ q).toBodyHinge.supportExtensor cd.e₀) = 0 := by
    rw [PanelHingeFramework.toBodyHinge_supportExtensor, PanelHingeFramework.ofNormals_normal,
      PanelHingeFramework.ofNormals_normal, PanelHingeFramework.ofNormals_ends, he₀rec,
      panelSupportExtensor_swap, map_neg, hρ₀e₀, neg_zero]
  -- (2) `ρ₀` vanishes on `C(qρ(a), qρ(b))` (KT eq. (6.66), `interior_hρe₀_of_baseWidening`), from
  -- the combination and the ends of `edge i`, from `v` to `a`, given by `hrec_G`.
  have hends_i : ends₀ e_a = (a, v) ∨ ends₀ e_a = (v, a) := by
    rcases hrec_G e_a v a hlea with h | h
    · exact Or.inr h
    · exact Or.inl h
  have hρe₀ : ρ₀ (panelSupportExtensor (fun j => qρ (a, j)) (fun j => qρ (b, j))) = 0 :=
    cd.interior_hρe₀_of_baseWidening h3 i h2i ends₀ hends_i hedgeGv
  -- (3) `hingeRow a b (-ρ₀)` lies in the row space of `ofNormals Gv ends₀ qρ` (KT eq. (6.66),
  -- `chainData_relabel_arm_hρGv`), from `hrec_G`, `hρ₀Gv` and the combination.
  obtain ⟨nGv, cGv, evGv, uvGv, vvGv, rvGv, hlinkGv, hrvGv, hcombGv⟩ := hedgeGv
  have hρGv : BodyHingeFramework.hingeRow a b (-ρ₀) ∈ Submodule.span K
      (PanelHingeFramework.ofNormals Gv ends₀ qρ).toBodyHinge.rigidityRows := by
    refine cd.chainData_relabel_arm_hρGv h3 i h2i cGv evGv uvGv vvGv rvGv hrec_G hrece₀
      (fun j => (Graph.removeVertex_isLink.mp (hlinkGv j)).1) hrvGv hcombGv.symm ?_ hρ₀Gv hρe₀base
    -- `hdeg1`: a term of the combination at an edge with the end `vtx 2` is at `edge 2`, as `vtx 2`
    -- is interior and `edge 1` meets `vtx 1`.
    intro j hj
    obtain ⟨hGlink, hu1, hv1⟩ := Graph.removeVertex_isLink.mp (hlinkGv j)
    obtain ⟨-, -, -, -, -, hlink_one, -⟩ := cd.splitOff_data_one (by omega)
    have hanchor : G.IsLink (evGv j) (cd.vtx ⟨2, by omega⟩) (vvGv j) ∨
        G.IsLink (evGv j) (uvGv j) (cd.vtx ⟨2, by omega⟩) := by
      rcases hj with h | h
      · exact Or.inl (h ▸ hGlink)
      · exact Or.inr (h ▸ hGlink)
    have hdt := cd.deg_two ⟨2, by omega⟩ (show 0 < (2 : ℕ) by omega)
    have hcl : evGv j = cd.edge ⟨1, by omega⟩ ∨ evGv j = cd.edge ⟨2, by omega⟩ := by
      rcases hanchor with h | h
      · simpa using hdt (evGv j) (vvGv j)
          (by rw [show (⟨2, by omega⟩ : Fin cd.d).castSucc = (⟨2, by omega⟩ : Fin (cd.d + 1)) from
            Fin.ext rfl]; exact h)
      · simpa using hdt (evGv j) (uvGv j)
          (by rw [show (⟨2, by omega⟩ : Fin cd.d).castSucc = (⟨2, by omega⟩ : Fin (cd.d + 1)) from
            Fin.ext rfl]; exact h.symm)
    rcases hcl with h | h
    · exfalso
      rcases hlink_one.eq_and_eq_or_eq_and_eq (h ▸ hGlink) with ⟨h1, _⟩ | ⟨h1, _⟩
      · exact hu1 h1.symm
      · exact hv1 h1.symm
    · exact h
  have hleG : ∀ {e u w}, Gv.IsLink e u w → G.IsLink e u w :=
    fun hlink => (Graph.removeVertex_isLink.mp hlink).1
  -- (4) `ends₀` gives each link of `G_1` its ends, for the `hrec'` of
  -- `chainData_interior_realization_hρGv` (from `hrec_G` and `he₀rec`).
  have hidx10 : (cd.vtx (⟨1, by omega⟩ : Fin cd.d).succ) = cd.vtx ⟨2, by omega⟩ :=
    congrArg cd.vtx (Fin.ext rfl)
  have hidx00 : (cd.vtx (⟨0, by omega⟩ : Fin cd.d).castSucc) = cd.vtx ⟨0, by omega⟩ :=
    congrArg cd.vtx (Fin.ext rfl)
  have hrec'_base : ∀ f x y, (G.splitOff (cd.vtx (⟨1, by omega⟩ : Fin cd.d).castSucc)
      (cd.vtx (⟨1, by omega⟩ : Fin cd.d).succ)
      (cd.vtx (⟨0, by omega⟩ : Fin cd.d).castSucc) cd.e₀).IsLink f x y →
      ends₀ f = (x, y) ∨ ends₀ f = (y, x) := by
    intro f x y hlink
    rw [Graph.splitOff_isLink] at hlink
    rcases hlink with ⟨hee₀, hGlink, _, _⟩ | ⟨rfl, _, _, _, _, hxy⟩
    · exact hrec_G f x y hGlink
    · -- `f = e₀`: `{x, y} = {vtx 2, vtx 0}`, and `he₀rec : ends₀ e₀ = (vtx 2, vtx 0)`.
      rw [hidx10, hidx00] at hxy
      rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl he₀rec
      · exact Or.inr he₀rec
  -- The selector `endsσρ₁`: `ends₀` with `e_a ↦ (v, a)` and `e_b ↦ (v, b)`.
  set endsσρ₁ : β → α × α := Function.update (Function.update ends₀ e_a (v, a)) e_b (v, b)
    with hendsσρ₁
  have hoff : ∀ e, e ≠ e_a → e ≠ e_b → endsσρ₁ e = ends₀ e := by
    intro e hea heb
    rw [hendsσρ₁, Function.update_of_ne heb, Function.update_of_ne hea]
  have hends_ea : endsσρ₁ e_a = (v, a) := by
    rw [hendsσρ₁, Function.update_of_ne heab, Function.update_self]
  have hends_eb : endsσρ₁ e_b = (v, b) := by rw [hendsσρ₁, Function.update_self]
  -- The links of `Gv` are not `e_a` or `e_b`, which meet `v ∉ V(Gv)`, and `endsσρ₁` gives them
  -- their ends.
  have hvVc : v ∉ V(Gv) := cd.notMem_vertexSet_removeVertex_castSucc i
  have hGv_off : ∀ {e u w}, Gv.IsLink e u w → e ≠ e_a ∧ e ≠ e_b := fun hlink =>
    ⟨hlea.ne_of_notMem hvVc (fun _ _ _ h => hleG h) hlink,
      hleb.ne_of_notMem hvVc (fun _ _ _ h => hleG h) hlink⟩
  have hends_Gv : ∀ e u w, Gv.IsLink e u w → Gv.IsLink e (endsσρ₁ e).1 (endsσρ₁ e).2 := by
    intro e u w hlink
    obtain ⟨hne_a, hne_b⟩ := hGv_off hlink
    rw [hoff e hne_a hne_b]
    rcases hrec_G e u w (hleG hlink) with he | he <;> rw [he]
    · exact hlink
    · exact hlink.symm
  have hne_Gv : ∀ e, Gv.IsLink e (endsσρ₁ e).1 (endsσρ₁ e).2 →
      (PanelHingeFramework.ofNormals Gv endsσρ₁ qρ).toBodyHinge.supportExtensor e ≠ 0 := by
    intro e hlink
    apply PanelHingeFramework.supportExtensor_ne_zero_of_isGeneralPosition
    · intro x y hxy
      rw [PanelHingeFramework.ofNormals_normal, PanelHingeFramework.ofNormals_normal]
      -- Two normals of `qρ` are linearly independent: `qρ (x,·) = q (σᵢ x, ·)`, and `σᵢ` is
      -- injective.
      exact hgp_seed (cd.shiftPerm i.castSucc x) (cd.shiftPerm i.castSucc y)
        ((cd.shiftPerm i.castSucc).injective.ne hxy)
    · rw [PanelHingeFramework.ofNormals_ends]; exact hlink.ne
  -- The bottom rows renamed along `σᵢ` by `L`, which is injective, so they stay linearly
  -- independent.
  set L : Module.Dual K (α → ScrewSpace K k) →ₗ[K] Module.Dual K (α → ScrewSpace K k) :=
    (LinearMap.funLeft K (ScrewSpace K k) (cd.shiftPerm i.castSucc).symm).dualMap with hL
  have hwL : LinearIndependent K (fun j => L (w j)) :=
    hw.map' _ (LinearMap.ker_eq_bot.2
      (LinearMap.dualMap_injective_of_surjective
        (LinearMap.funLeft_surjective_of_injective _ _ (cd.shiftPerm i.castSucc).symm
          (Equiv.injective _))))
  -- `ends₀` gives every link of `G − vtx 1` its ends (for the `hrec` of
  -- `chainData_bottom_relabel`).
  have hrec_Gv1 : ∀ e x y, (G.removeVertex (cd.vtx (⟨1, by omega⟩ : Fin cd.d).castSucc)).IsLink
      e x y → ends₀ e = (x, y) ∨ ends₀ e = (y, x) :=
    fun e x y hlink => hrec_G e x y (Graph.removeVertex_isLink.mp hlink).1
  -- The indices `.castSucc` of `Fin cd.d`, at which `chainData_bottom_relabel` states the split, as
  -- those of `Fin (cd.d + 1)`, at which `chainData_fire_discriminator` states it.
  have hv0c : cd.vtx (⟨0, by omega⟩ : Fin cd.d).castSucc = cd.vtx ⟨0, by omega⟩ :=
    congrArg cd.vtx (Fin.ext rfl)
  have hv2c : cd.vtx (⟨2, by omega⟩ : Fin cd.d).castSucc = cd.vtx ⟨2, by omega⟩ :=
    congrArg cd.vtx (Fin.ext rfl)
  -- The bottom rows at the orientation `(v₂, v₀)` of `chainData_bottom_relabel`:
  -- `hingeRow v₀ v₂ ρ' = hingeRow v₂ v₀ (-ρ')`, and `-ρ'` vanishes on the hinge too.
  have hwmem_norm : ∀ j, w j ∈ (PanelHingeFramework.ofNormals
        (G.removeVertex (cd.vtx (⟨1, by omega⟩ : Fin cd.d).castSucc)) ends₀
        q).toBodyHinge.rigidityRows
      ∨ ∃ ρ' : Module.Dual K (ScrewSpace K k),
        ρ' (panelSupportExtensor (fun j => q (cd.vtx (⟨2, by omega⟩ : Fin cd.d).castSucc, j))
          (fun j => q (cd.vtx (⟨0, by omega⟩ : Fin cd.d).castSucc, j))) = 0 ∧
        w j = BodyHingeFramework.hingeRow (cd.vtx (⟨2, by omega⟩ : Fin cd.d).castSucc)
          (cd.vtx (⟨0, by omega⟩ : Fin cd.d).castSucc) ρ' := by
    intro j
    rcases hwmem' j with hgen | ⟨ρ', hρ'e₀, hwj⟩
    · exact Or.inl hgen
    · -- from `(v₀, v₂)` to `(v₂, v₀)`, by `ρ' ↦ -ρ'`.
      refine Or.inr ⟨-ρ', ?_, ?_⟩
      · rw [hv0c, hv2c, LinearMap.neg_apply, panelSupportExtensor_swap, map_neg, hρ'e₀,
          neg_zero, neg_zero]
      · rw [hwj, hv0c, hv2c, BodyHingeFramework.hingeRow_swap]
  -- `u_i = candidateVtx i = vtx i.succ = a`.
  have hcandVtx : cd.candidateVtx i = a := cd.candidateVtx_succ_eq h0i
  -- The realization, by `chainData_interior_realization_hρGv`.
  refine PanelHingeFramework.chainData_interior_realization_hρGv (k := k) cd i h2i (q := q)
    (ends₀ := ends₀)
    (ρ₀ := ρ₀) (n' := n') endsσρ₁ hoff hends_ea hends_eb hends_Gv hne_Gv ?hLn ?hgab ?hρgate
    ?hρe₀ hρGv hrec'_base (ιb := ιb) (w := fun j => L (w j)) ?hwcard hwL ?hwmem hdef
  case hLn => rw [hcandVtx] at hLI; exact hLI
  case hgab => exact hgp_seed a v (cd.castSucc_ne_succ i).symm
  case hρgate => rw [hcandVtx] at hgate; exact hgate
  case hρe₀ => exact hρe₀
  case hwcard => exact hwcard
  case hwmem =>
    -- each renamed row, by `chainData_bottom_relabel`, at the selector `candidateEnds i ends₀`;
    -- `chainData_interior_realization_hρGv` passes to `endsσρ₁`. The `1 < i` is pulled out of the
    -- call so `exact` stays syntactic (TACTICS-QUIRKS §43).
    intro j
    have hi1 : 1 < (i : ℕ) := by omega
    have he₀rec' : ends₀ cd.e₀ = (cd.vtx (⟨2, by omega⟩ : Fin cd.d).castSucc,
        cd.vtx (⟨0, by omega⟩ : Fin cd.d).castSucc) := by rw [hv2c, hv0c]; exact he₀rec
    exact PanelHingeFramework.chainData_bottom_relabel cd i hi1 hrec_Gv1 he₀rec' (hwmem_norm j)

/-- **The framework `(G, p_i)` for `2 ≤ i`** (a step of `lem:case-III-chain-dispatch`): let `cd` be
a chain of length `d ≥ 3` in a simple `G` of deficiency `0`, and `2 ≤ i`. Given what
`chainData_fire_discriminator` gives at its selector `ends` (general position on `G_1`, the form
`ρ₀`, the bottom rows, the combination, the normal `n'` at the panel of `u_i`, and `ends` on the
links of `G_1`), `G` has a generic full-rank realization.

The proof. The selector `ends₀` is `ends` with `e₀ ↦ (v₂, v₀)`, `edge 0 ↦ (v₀, v₁)` and
`edge 1 ↦ (v₁, v₂)`. None of the three edges is a link of `G − v₁`: the last two meet `v₁`, and
`e₀ ∉ E(G)`. So on the links of `G − v₁` the selector `ends₀` is `ends`, and the rows, the hinge-row
blocks and the facts at `ends` hold at `ends₀` (`rigidityRows_ofNormals_congr_ends`). As `ends`
gives each link of `G_1` its ends, `ends₀` gives each link of `G` its ends
(`Graph.ChainData.fullLink_recording_of_splitOff_recording`), and `chainData_dispatch_interior`
gives the realization. -/
theorem PanelHingeFramework.chainData_dispatch_interior_of_discriminator [Infinite K]
    [Finite α] [Finite β]
    {G : Graph α β} {n : ℕ} (cd : G.ChainData n) (h3 : 3 ≤ cd.d) (hSimple : G.Simple)
    (i : Fin cd.d) (h2i : 2 ≤ (i : ℕ))
    {q : α × Fin (k + 2) → K} {ends : β → α × α}
    {ρ₀ : Module.Dual K (ScrewSpace K k)}
    {w : Fin (screwDim k * (V(G.splitOff (cd.vtx ⟨1, by omega⟩) (cd.vtx ⟨0, by omega⟩)
          (cd.vtx ⟨2, by omega⟩) cd.e₀).ncard - 1)) → Module.Dual K (α → ScrewSpace K k)}
    {n' : Fin (k + 2) → K}
    -- What `chainData_fire_discriminator` gives, at the split `(v, a, b) = (vtx 1, vtx 0, vtx 2)`
    -- and the selector `ends`:
    (hgp : (PanelHingeFramework.ofNormals (G.splitOff (cd.vtx ⟨1, by omega⟩) (cd.vtx ⟨0, by omega⟩)
      (cd.vtx ⟨2, by omega⟩) cd.e₀) ends q).IsGeneralPosition)
    (hρ₀e₀ : ρ₀ (panelSupportExtensor (fun j => q (cd.vtx ⟨0, by omega⟩, j))
      (fun j => q (cd.vtx ⟨2, by omega⟩, j))) = 0)
    (hw : LinearIndependent K w)
    (hwmem' : ∀ j, w j ∈ (PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx ⟨1, by omega⟩))
        ends q).toBodyHinge.rigidityRows ∨
      ∃ ρ' : Module.Dual K (ScrewSpace K k),
        ρ' (panelSupportExtensor (fun j => q (cd.vtx ⟨0, by omega⟩, j))
          (fun j => q (cd.vtx ⟨2, by omega⟩, j))) = 0 ∧
        w j = BodyHingeFramework.hingeRow (cd.vtx ⟨0, by omega⟩) (cd.vtx ⟨2, by omega⟩) ρ')
    (hedgeGv :
      ∃ (nGv : ℕ) (cGv : Fin nGv → K) (evGv : Fin nGv → β) (uvGv vvGv : Fin nGv → α)
          (rvGv : Fin nGv → Module.Dual K (ScrewSpace K k)),
        (∀ j, (G.removeVertex (cd.vtx ⟨1, by omega⟩)).IsLink (evGv j) (uvGv j) (vvGv j)) ∧
        (∀ j, rvGv j ∈ (PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx ⟨1, by omega⟩))
          ends q).toBodyHinge.hingeRowBlock (evGv j)) ∧
        BodyHingeFramework.hingeRow (cd.vtx ⟨0, by omega⟩) (cd.vtx ⟨2, by omega⟩) ρ₀
          = ∑ j, cGv j • BodyHingeFramework.hingeRow (uvGv j) (vvGv j) (rvGv j))
    (hLI : LinearIndependent K ![fun j => q (cd.candidateVtx i, j), n'])
    (hgate : ρ₀ (panelSupportExtensor (fun j => q (cd.candidateVtx i, j)) n') ≠ 0)
    (hρ₀Gv : BodyHingeFramework.hingeRow (cd.vtx ⟨0, by omega⟩) (cd.vtx ⟨2, by omega⟩) ρ₀ ∈
      Submodule.span K (PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx ⟨1, by omega⟩))
        ends q).toBodyHinge.rigidityRows)
    (hrecGab : ∀ f x y, (G.splitOff (cd.vtx ⟨1, by omega⟩) (cd.vtx ⟨0, by omega⟩)
        (cd.vtx ⟨2, by omega⟩) cd.e₀).IsLink f x y → ends f = (x, y) ∨ ends f = (y, x))
    (hdef : G.deficiency n = 0) :
    PanelHingeFramework.HasGenericFullRankRealization K k n G := by
  classical
  have : Fintype α := Fintype.ofFinite α
  have hGloop : G.Loopless := hSimple.toLoopless
  -- The vertices `vtx 0`, `vtx 1` and `vtx 2` (indices of `Fin (cd.d + 1)`, as
  -- `chainData_dispatch_interior` states them) are not `set`-abbreviated: `w`'s type mentions
  -- `cd.vtx ⟨0/1/2, _⟩`, so `set` would shadow the hypotheses on `w` (`hw`, `hwmem'`) against the
  -- final `exact`.
  set Gv := G.removeVertex (cd.vtx (⟨1, by omega⟩ : Fin (cd.d + 1))) with hGv
  -- The two edges at `v₁` (`edge 0 : v₀v₁`, `edge 1 : v₁v₂`) and `e₀`, the three edges at which
  -- `ends₀` changes `ends`. None is a link of `Gv`: the first two meet `v₁`, and `e₀ ∉ E(G)`.
  obtain ⟨-, -, -, he01, hl0, hl1, -⟩ := cd.splitOff_data_one (by omega)
  have he₀ne0 : cd.e₀ ≠ cd.edge ⟨0, by omega⟩ := fun h =>
    cd.e₀_fresh (h ▸ hl0.edge_mem)
  have he₀ne1 : cd.e₀ ≠ cd.edge ⟨1, by omega⟩ := fun h =>
    cd.e₀_fresh (h ▸ hl1.edge_mem)
  -- The selector `ends₀`: `ends` with `e₀ ↦ (v₂, v₀)`, `edge 0 ↦ (v₀, v₁)` and `edge 1 ↦ (v₁, v₂)`.
  set ends₀ : β → α × α :=
    Function.update (Function.update (Function.update ends cd.e₀
        (cd.vtx ⟨2, by omega⟩, cd.vtx ⟨0, by omega⟩))
      (cd.edge ⟨0, by omega⟩) (cd.vtx ⟨0, by omega⟩, cd.vtx ⟨1, by omega⟩))
      (cd.edge ⟨1, by omega⟩) (cd.vtx ⟨1, by omega⟩, cd.vtx ⟨2, by omega⟩) with hends₀
  -- The values of `ends₀` at the three edges.
  have he₀rec : ends₀ cd.e₀ = (cd.vtx ⟨2, by omega⟩, cd.vtx ⟨0, by omega⟩) := by
    simp only [hends₀, Function.update_of_ne he₀ne1, Function.update_of_ne he₀ne0,
      Function.update_self]
  have hr0 : ends₀ (cd.edge ⟨0, by omega⟩) = (cd.vtx ⟨0, by omega⟩, cd.vtx ⟨1, by omega⟩) := by
    rw [hends₀, Function.update_of_ne he01, Function.update_self]
  have hr1 : ends₀ (cd.edge ⟨1, by omega⟩) = (cd.vtx ⟨1, by omega⟩, cd.vtx ⟨2, by omega⟩) := by
    rw [hends₀, Function.update_self]
  -- `ends₀` agrees with `ends` off the three edges.
  have hoff : ∀ e, e ≠ cd.e₀ → e ≠ cd.edge ⟨0, by omega⟩ → e ≠ cd.edge ⟨1, by omega⟩ →
      ends₀ e = ends e := by
    intro e he₀ hea heb
    simp only [hends₀, Function.update_of_ne heb, Function.update_of_ne hea,
      Function.update_of_ne he₀]
  -- No link of `Gv = G − v₁` is one of the three edges: `edge 0` and `edge 1` meet `v₁ ∉ V(Gv)`,
  -- and `e₀ ∉ E(G)`.
  have hvVc : cd.vtx (⟨1, by omega⟩ : Fin (cd.d + 1)) ∉ V(Gv) :=
    cd.notMem_vertexSet_removeVertex_castSucc ⟨1, by omega⟩
  have hleG : ∀ e u w, Gv.IsLink e u w → G.IsLink e u w :=
    fun _ _ _ hlink => (Graph.removeVertex_isLink.mp hlink).1
  have hGv_off : ∀ {e u w}, Gv.IsLink e u w →
      e ≠ cd.e₀ ∧ e ≠ cd.edge ⟨0, by omega⟩ ∧ e ≠ cd.edge ⟨1, by omega⟩ := fun hlink =>
    ⟨fun he => cd.e₀_fresh (he ▸ (hleG _ _ _ hlink).edge_mem), hl0.ne_of_notMem hvVc hleG hlink,
      hl1.ne_of_notMem hvVc hleG hlink⟩
  -- `ends₀ = ends` on every link of `Gv`, so the two frameworks have the same rows and hinge-row
  -- blocks there.
  have hagreeGv : ∀ e u w, Gv.IsLink e u w → ends₀ e = ends e := by
    intro e u w hlink
    obtain ⟨h0, ha, hb⟩ := hGv_off hlink
    exact hoff e h0 ha hb
  have hrows : (PanelHingeFramework.ofNormals Gv ends₀ q).toBodyHinge.rigidityRows
      = (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge.rigidityRows :=
    PanelHingeFramework.rigidityRows_ofNormals_congr_ends q hagreeGv
  have hblock : ∀ e u w, Gv.IsLink e u w →
      (PanelHingeFramework.ofNormals Gv ends₀ q).toBodyHinge.hingeRowBlock e =
        (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge.hingeRowBlock e := by
    intro e u w hlink
    simp only [BodyHingeFramework.hingeRowBlock, PanelHingeFramework.toBodyHinge_supportExtensor,
      PanelHingeFramework.ofNormals_ends, PanelHingeFramework.ofNormals_normal,
      hagreeGv e u w hlink]
  -- (a) `ends₀` gives each link of `G` its ends (`fullLink_recording_of_splitOff_recording`), from
  -- the links of `G_1` (`hrecGab`, and `he₀rec` at `e₀`) and the two edges at `v₁`.
  have hrecGab' : ∀ f x y, (G.splitOff (cd.vtx (⟨1, by omega⟩ : Fin cd.d).castSucc)
      (cd.vtx (⟨0, by omega⟩ : Fin cd.d).castSucc) (cd.vtx (⟨2, by omega⟩ : Fin cd.d).castSucc)
      cd.e₀).IsLink f x y → ends₀ f = (x, y) ∨ ends₀ f = (y, x) := by
    intro f x y hlink
    -- the indices `.castSucc` of the split, as those of `Fin (cd.d + 1)`.
    have hc1 : (⟨1, by omega⟩ : Fin cd.d).castSucc = (⟨1, by omega⟩ : Fin (cd.d + 1)) := Fin.ext rfl
    have hc0 : (⟨0, by omega⟩ : Fin cd.d).castSucc = (⟨0, by omega⟩ : Fin (cd.d + 1)) := Fin.ext rfl
    have hc2 : (⟨2, by omega⟩ : Fin cd.d).castSucc = (⟨2, by omega⟩ : Fin (cd.d + 1)) := Fin.ext rfl
    rw [hc1, hc0, hc2] at hlink
    -- a link `f` of `G_1` is an edge of `G` (`f ≠ e₀`) or the new edge `e₀`.
    rw [Graph.splitOff_isLink] at hlink
    rcases hlink with ⟨hfne, hGlink, hxne, hyne⟩ | ⟨rfl, _, _, _, _, hxy⟩
    · -- an edge of `G` with the ends `x, y ≠ v₁`: it is not `e₀`, `edge 0` or `edge 1`, so
      -- `ends₀ f = ends f`, given by `hrecGab`.
      have hfa : f ≠ cd.edge ⟨0, by omega⟩ := by
        rintro rfl
        rcases hl0.eq_and_eq_or_eq_and_eq hGlink with ⟨h, _⟩ | ⟨h, _⟩
        · exact hxne h.symm
        · exact hyne h.symm
      have hfb : f ≠ cd.edge ⟨1, by omega⟩ := by
        rintro rfl
        rcases hl1.eq_and_eq_or_eq_and_eq hGlink with ⟨h, _⟩ | ⟨h, _⟩
        · exact hxne h.symm
        · exact hyne h.symm
      rw [hoff f hfne hfa hfb]
      exact hrecGab f x y (Graph.splitOff_isLink.mpr (Or.inl ⟨hfne, hGlink, hxne, hyne⟩))
    · -- `f = e₀`: `{x, y} = {v₀, v₂}`, and `ends₀ e₀ = (v₂, v₀)`.
      rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inr he₀rec
      · exact Or.inl he₀rec
  have hrec_G : ∀ f x y, G.IsLink f x y → ends₀ f = (x, y) ∨ ends₀ f = (y, x) :=
    cd.fullLink_recording_of_splitOff_recording h3 hrecGab' (Or.inl hr0) (Or.inl hr1)
  -- (b) The facts on `Gv` at `ends₀`.
  have hwmem'₀ : ∀ j, w j ∈ (PanelHingeFramework.ofNormals Gv ends₀ q).toBodyHinge.rigidityRows ∨
      ∃ ρ' : Module.Dual K (ScrewSpace K k),
        ρ' (panelSupportExtensor (fun j => q (cd.vtx ⟨0, by omega⟩, j))
          (fun j => q (cd.vtx ⟨2, by omega⟩, j))) = 0 ∧
        w j = BodyHingeFramework.hingeRow (cd.vtx ⟨0, by omega⟩) (cd.vtx ⟨2, by omega⟩) ρ' := by
    intro j
    rcases hwmem' j with hgen | hcand
    · exact Or.inl (by rw [hrows]; exact hgen)
    · exact Or.inr hcand
  have hedgeGv₀ :
      ∃ (nGv : ℕ) (cGv : Fin nGv → K) (evGv : Fin nGv → β) (uvGv vvGv : Fin nGv → α)
          (rvGv : Fin nGv → Module.Dual K (ScrewSpace K k)),
        (∀ j, Gv.IsLink (evGv j) (uvGv j) (vvGv j)) ∧
        (∀ j, rvGv j ∈ (PanelHingeFramework.ofNormals Gv ends₀ q).toBodyHinge.hingeRowBlock
          (evGv j)) ∧
        BodyHingeFramework.hingeRow (cd.vtx ⟨0, by omega⟩) (cd.vtx ⟨2, by omega⟩) ρ₀
          = ∑ j, cGv j • BodyHingeFramework.hingeRow (uvGv j) (vvGv j) (rvGv j) := by
    obtain ⟨nGv, cGv, evGv, uvGv, vvGv, rvGv, hlinkGv, hrvGv, hcomb⟩ := hedgeGv
    exact ⟨nGv, cGv, evGv, uvGv, vvGv, rvGv, hlinkGv,
      fun j => (hblock _ _ _ (hlinkGv j)).symm ▸ hrvGv j, hcomb⟩
  have hρ₀Gv₀ : BodyHingeFramework.hingeRow (cd.vtx ⟨0, by omega⟩) (cd.vtx ⟨2, by omega⟩) ρ₀ ∈
      Submodule.span K (PanelHingeFramework.ofNormals Gv ends₀ q).toBodyHinge.rigidityRows := by
    rw [hrows]; exact hρ₀Gv
  -- (c) Any two normals are linearly independent, by general position.
  have hgp_seed : ∀ x y : α, x ≠ y →
      LinearIndependent K ![fun j => q (x, j), fun j => q (y, j)] := by
    intro x y hxy
    have := hgp x y hxy
    rwa [PanelHingeFramework.ofNormals_normal, PanelHingeFramework.ofNormals_normal] at this
  -- The number of bottom rows, `D(|V(G_1)| − 1) = D(|V(G)| − 2)`.
  have hcard_Gab : V(G.splitOff (cd.vtx ⟨1, by omega⟩) (cd.vtx ⟨0, by omega⟩)
      (cd.vtx ⟨2, by omega⟩) cd.e₀).ncard = V(G).ncard - 1 := by
    rw [Graph.vertexSet_splitOff,
      Set.ncard_sdiff_singleton_of_mem (cd.vtx_mem ⟨1, by omega⟩)]
  have hwcard : Nat.card (Fin (screwDim k *
      (V(G.splitOff (cd.vtx ⟨1, by omega⟩) (cd.vtx ⟨0, by omega⟩)
        (cd.vtx ⟨2, by omega⟩) cd.e₀).ncard - 1))) = screwDim k * (V(G).ncard - 2) := by
    rw [Nat.card_fin, hcard_Gab, Nat.sub_sub]
  -- The realization, by `chainData_dispatch_interior` at `ends₀`.
  exact PanelHingeFramework.chainData_dispatch_interior (k := k) cd h3 hSimple i h2i
    hwcard hgp_seed hrec_G he₀rec hρ₀e₀ hw hwmem'₀ hedgeGv₀ hLI hgate hρ₀Gv₀ hdef

/-- **The framework `(G, p_i)` for `i ≤ 1`** (a step of `lem:case-III-chain-dispatch`): let `cd` be
a chain of length `d ≥ 2` in a simple `G` of deficiency `0`, and `i ≤ 1`. Given what
`chainData_fire_discriminator` gives at its selector `ends` (general position on `G_1`, `ends` on
the links of `G_1`, the form `ρ₀`, the bottom rows, and the normal `n'` at the panel of `u_i`),
`G` has a generic full-rank realization. Katoh and Tanigawa's `(G, p_0)` and `(G, p_1)` (KT
eqs. (6.47) and (6.48), p. 692) put `v₁` back, with the hinge `L_0` in the panel of `u_0 = v₀`, and
`L_1` in that of `u_1 = v₂`.

The proof, as in the proof of `lem:case-III-chain-dispatch` for `i ≤ 1`, and as
`case_III_candidate_dispatch` treats `u = 0` and `u = 1`. At the split `(v, a, b) = (v₁, v₀, v₂)`,
with `(e_a, e_b) = (edge 0, edge 1)` and the selector `ends₁`, `ends` with `edge 0 ↦ (v₁, v₀)` and
`edge 1 ↦ (v₁, v₂)`, `case_III_arm_realization` for `i = 0` and `case_III_arm_realization_M2` for
`i = 1` give the realization from `ρ₀` and the bottom rows. The two edges meet `v₁`, so they are not
links of `G − v₁`, and the rows at `ends` and at `ends₁` are the same
(`rigidityRows_ofNormals_congr_ends`). `ends`, and so `ends₁`, records the links of `G − v₁`, a
subgraph of `G_1` as `e₀ ∉ E(G)` (`Graph.removeVertex_le_splitOff`). -/
theorem PanelHingeFramework.chainData_dispatch_floor_of_discriminator [Infinite K]
    [Finite α] [Finite β]
    {G : Graph α β} {n : ℕ} (cd : G.ChainData n) (hd2 : 2 ≤ cd.d) (hSimple : G.Simple)
    (i : Fin cd.d) (h1i : (i : ℕ) ≤ 1)
    {q : α × Fin (k + 2) → K} {ends : β → α × α}
    {ρ₀ : Module.Dual K (ScrewSpace K k)}
    {w : Fin (screwDim k * (V(G.splitOff (cd.vtx ⟨1, by omega⟩) (cd.vtx ⟨0, by omega⟩)
          (cd.vtx ⟨2, by omega⟩) cd.e₀).ncard - 1)) → Module.Dual K (α → ScrewSpace K k)}
    {n' : Fin (k + 2) → K}
    -- What `chainData_fire_discriminator` gives, at the split `(v, a, b) = (vtx 1, vtx 0, vtx 2)`
    -- and the selector `ends`:
    (hgp : (PanelHingeFramework.ofNormals (G.splitOff (cd.vtx ⟨1, by omega⟩) (cd.vtx ⟨0, by omega⟩)
      (cd.vtx ⟨2, by omega⟩) cd.e₀) ends q).IsGeneralPosition)
    (hends' : PanelHingeFramework.RecordsLinks (G.splitOff (cd.vtx ⟨1, by omega⟩)
      (cd.vtx ⟨0, by omega⟩) (cd.vtx ⟨2, by omega⟩) cd.e₀) ends)
    (hρ₀e₀ : ρ₀ (panelSupportExtensor (fun j => q (cd.vtx ⟨0, by omega⟩, j))
      (fun j => q (cd.vtx ⟨2, by omega⟩, j))) = 0)
    (hw : LinearIndependent K w)
    (hwmem' : ∀ j, w j ∈ (PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx ⟨1, by omega⟩))
        ends q).toBodyHinge.rigidityRows ∨
      ∃ ρ' : Module.Dual K (ScrewSpace K k),
        ρ' (panelSupportExtensor (fun j => q (cd.vtx ⟨0, by omega⟩, j))
          (fun j => q (cd.vtx ⟨2, by omega⟩, j))) = 0 ∧
        w j = BodyHingeFramework.hingeRow (cd.vtx ⟨0, by omega⟩) (cd.vtx ⟨2, by omega⟩) ρ')
    (hLI : LinearIndependent K ![fun j => q (cd.candidateVtx i, j), n'])
    (hgate : ρ₀ (panelSupportExtensor (fun j => q (cd.candidateVtx i, j)) n') ≠ 0)
    (hρ₀Gv : BodyHingeFramework.hingeRow (cd.vtx ⟨0, by omega⟩) (cd.vtx ⟨2, by omega⟩) ρ₀ ∈
      Submodule.span K (PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx ⟨1, by omega⟩))
        ends q).toBodyHinge.rigidityRows)
    (hdef : G.deficiency n = 0) :
    PanelHingeFramework.HasGenericFullRankRealization K k n G := by
  classical
  have : Fintype α := Fintype.ofFinite α
  have hGloop : G.Loopless := hSimple.toLoopless
  -- The split `(v, a, b) = (vtx 1, vtx 0, vtx 2)`, `(e_a, e_b) = (edge 0, edge 1)`. The vertices
  -- are not `set`-abbreviated: `w`'s type mentions `cd.vtx ⟨0/1/2, _⟩` (inside `V(G.splitOff …)`),
  -- so `set` would shadow the hypotheses on `w` (`hw`, `hwmem'`); only `Gv`, which does not appear
  -- in `w`'s type, is abbreviated.
  set Gv := G.removeVertex (cd.vtx (⟨1, by omega⟩ : Fin (cd.d + 1))) with hGv
  have : Gv.Loopless := hGloop.mono (hGv ▸ Graph.removeVertex_le G (cd.vtx ⟨1, by omega⟩))
  -- The two edges at `v = vtx 1`, from `v`, their distinctness, and the edges of `G` at `v`
  -- (`Graph.ChainData.splitOff_data_one`), as in `chainData_fire_discriminator`.
  obtain ⟨hav, hbv, hba, heab, hlea, hleb, hclv⟩ := cd.splitOff_data_one hd2
  have hvG : cd.vtx (⟨1, by omega⟩ : Fin (cd.d + 1)) ∈ V(G) := cd.vtx_mem _
  have haG : cd.vtx (⟨0, by omega⟩ : Fin (cd.d + 1)) ∈ V(G) := cd.vtx_mem _
  have hbG : cd.vtx (⟨2, by omega⟩ : Fin (cd.d + 1)) ∈ V(G) := cd.vtx_mem _
  -- Facts on `Gv` and `G`, as in `case_III_candidate_dispatch`.
  have hvVc : cd.vtx (⟨1, by omega⟩ : Fin (cd.d + 1)) ∉ V(Gv) := by
    rw [hGv, Graph.vertexSet_removeVertex]; exact fun h => h.2 rfl
  have haVc : cd.vtx (⟨0, by omega⟩ : Fin (cd.d + 1)) ∈ V(Gv) := by
    rw [hGv, Graph.vertexSet_removeVertex]; exact ⟨haG, hav⟩
  have hbVc : cd.vtx (⟨2, by omega⟩ : Fin (cd.d + 1)) ∈ V(Gv) := by
    rw [hGv, Graph.vertexSet_removeVertex]; exact ⟨hbG, hbv⟩
  have hleG : ∀ e u w, Gv.IsLink e u w → G.IsLink e u w := by
    intro e u w hlink; rw [hGv, Graph.removeVertex_isLink] at hlink; exact hlink.1
  have hGv_off : ∀ {e u w}, Gv.IsLink e u w →
      e ≠ cd.edge ⟨0, by omega⟩ ∧ e ≠ cd.edge ⟨1, by omega⟩ := fun hlink =>
    ⟨hlea.ne_of_notMem hvVc hleG hlink, hleb.ne_of_notMem hvVc hleG hlink⟩
  have hsplitG : ∀ e u w, G.IsLink e u w →
      e = cd.edge ⟨0, by omega⟩ ∨ e = cd.edge ⟨1, by omega⟩ ∨ Gv.IsLink e u w := by
    intro e u w hlink
    by_cases hu : u = cd.vtx ⟨1, by omega⟩
    · subst u; rcases hclv e w hlink with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
    · by_cases hw : w = cd.vtx ⟨1, by omega⟩
      · subst w; rcases hclv e u hlink.symm with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (by rw [hGv, Graph.removeVertex_isLink]; exact ⟨hlink, hu, hw⟩))
  have hVone : 1 ≤ V(Gv).ncard := by
    rw [hGv, Graph.vertexSet_removeVertex, Set.ncard_sdiff_singleton_of_mem hvG]
    have h2 : 2 ≤ V(G).ncard := by
      calc 2 = ({cd.vtx (⟨0, by omega⟩ : Fin (cd.d + 1)), cd.vtx ⟨2, by omega⟩} : Set α).ncard := by
            rw [Set.ncard_pair hba.symm]
        _ ≤ V(G).ncard := Set.ncard_le_ncard (by
            intro x hx; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
            rcases hx with rfl | rfl <;> [exact haG; exact hbG]) (Set.toFinite _)
    omega
  have hVcard : V(G).ncard = V(Gv).ncard + 1 := by
    rw [hGv, Graph.vertexSet_removeVertex, Set.ncard_sdiff_singleton_of_mem hvG]
    have : 1 ≤ V(G).ncard := Set.ncard_pos (Set.toFinite _) |>.mpr ⟨_, hvG⟩
    omega
  have hcard : V(G.splitOff (cd.vtx ⟨1, by omega⟩) (cd.vtx ⟨0, by omega⟩)
      (cd.vtx ⟨2, by omega⟩) cd.e₀).ncard = V(Gv).ncard := by
    rw [hGv, Graph.vertexSet_splitOff, Graph.vertexSet_removeVertex]
  -- Any two normals are linearly independent, by general position.
  have hgp_seed : ∀ x y : α, x ≠ y →
      LinearIndependent K ![fun j => q (x, j), fun j => q (y, j)] := by
    intro x y hxy
    have := hgp x y hxy
    rwa [PanelHingeFramework.ofNormals_normal, PanelHingeFramework.ofNormals_normal] at this
  -- The selector `ends₁`: `ends` with `edge 0 ↦ (v₁, v₀)` and `edge 1 ↦ (v₁, v₂)`.
  set ends₁ : β → α × α := Function.update (Function.update ends (cd.edge ⟨0, by omega⟩)
      (cd.vtx ⟨1, by omega⟩, cd.vtx ⟨0, by omega⟩))
    (cd.edge ⟨1, by omega⟩) (cd.vtx ⟨1, by omega⟩, cd.vtx ⟨2, by omega⟩) with hends₁
  have hends₁_off : ∀ {e}, e ≠ cd.edge ⟨0, by omega⟩ → e ≠ cd.edge ⟨1, by omega⟩ →
      ends₁ e = ends e := by
    intro e hea heb
    rw [hends₁, Function.update_of_ne heb, Function.update_of_ne hea]
  have hcongr : (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge.rigidityRows
      = (PanelHingeFramework.ofNormals Gv ends₁ q).toBodyHinge.rigidityRows :=
    PanelHingeFramework.rigidityRows_ofNormals_congr_ends q
      (fun e u w hlink => (hends₁_off (hGv_off hlink).1 (hGv_off hlink).2).symm)
  have hends_ea₁ : ends₁ (cd.edge ⟨0, by omega⟩)
      = (cd.vtx ⟨1, by omega⟩, cd.vtx ⟨0, by omega⟩) := by
    rw [hends₁, Function.update_of_ne heab, Function.update_self]
  have hends_eb₁ : ends₁ (cd.edge ⟨1, by omega⟩)
      = (cd.vtx ⟨1, by omega⟩, cd.vtx ⟨2, by omega⟩) := by
    rw [hends₁, Function.update_self]
  have hends_Gv₁ : ∀ e u w, Gv.IsLink e u w → Gv.IsLink e (ends₁ e).1 (ends₁ e).2 := by
    intro e u w hlink
    obtain ⟨hne_a, hne_b⟩ := hGv_off hlink
    rw [hends₁_off hne_a hne_b]
    exact (hends'.mono (G.removeVertex_le_splitOff cd.e₀_fresh)).isLink hlink
  have hne_Gv₁ : ∀ e, Gv.IsLink e (ends₁ e).1 (ends₁ e).2 →
      (PanelHingeFramework.ofNormals Gv ends₁ q).toBodyHinge.supportExtensor e ≠ 0 := by
    intro e hlink
    apply PanelHingeFramework.supportExtensor_ne_zero_of_isGeneralPosition
    · intro x y hxy
      rw [PanelHingeFramework.ofNormals_normal, PanelHingeFramework.ofNormals_normal]
      exact hgp_seed x y hxy
    · rw [PanelHingeFramework.ofNormals_ends]; exact hlink.ne
  -- The number of bottom rows, `D(|V(G_1)| − 1) = D(|V(Gv)| − 1)`.
  have hwcard : Nat.card (Fin (screwDim k * (V(G.splitOff (cd.vtx ⟨1, by omega⟩)
      (cd.vtx ⟨0, by omega⟩) (cd.vtx ⟨2, by omega⟩) cd.e₀).ncard - 1)))
      = screwDim k * (V(Gv).ncard - 1) := by rw [Nat.card_fin, hcard]
  -- The two cases: `i = 0`, with `n'` at the panel of `a = candidateVtx 0`, and `i = 1`, with `n'`
  -- at that of `b = candidateVtx 1`.
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h1i with hi0 | hi1
  · -- `i = 0`: `case_III_arm_realization`, with `L` in the panel of `a = vtx 0`.
    -- `candidateVtx i = vtx 0 = vtx ⟨0, _⟩`.
    rw [cd.candidateVtx_zero i hi0,
      show cd.vtx (0 : Fin (cd.d + 1)) = cd.vtx ⟨0, by omega⟩ from rfl] at hLI hgate
    refine PanelHingeFramework.case_III_arm_realization (k := k) G Gv ends₁ (q := q)
      (v := cd.vtx ⟨1, by omega⟩) (a := cd.vtx ⟨0, by omega⟩) (b := cd.vtx ⟨2, by omega⟩)
      (e_a := cd.edge ⟨0, by omega⟩) (e_b := cd.edge ⟨1, by omega⟩) (n' := n')
      hvVc haVc hbVc hlea hleb hends_ea₁ hends_eb₁ heab hleG hsplitG hends_Gv₁ hne_Gv₁
      hVone hVcard hLI (hgp_seed _ _ hba.symm) hgate hρ₀e₀ ?_ (ιb := _) (w := w) hwcard hw ?_ hdef
    · rw [← hcongr]; exact hρ₀Gv
    · intro j
      rcases hwmem' j with hgen | hcand
      · exact Or.inl (by rw [← hcongr]; exact hgen)
      · exact Or.inr hcand
  · -- `i = 1`: `case_III_arm_realization_M2`, with `L` in the panel of `b = vtx 2`.
    -- `candidateVtx i = vtx ⟨i+1, _⟩ = vtx ⟨2, _⟩`.
    rw [cd.candidateVtx_succ (by omega),
      show cd.vtx ⟨(i : ℕ) + 1, by omega⟩ = cd.vtx ⟨2, by omega⟩ from
        congrArg _ (Fin.ext (show (i : ℕ) + 1 = 2 by omega))] at hLI hgate
    refine PanelHingeFramework.case_III_arm_realization_M2 (k := k) G Gv ends₁ (q := q)
      (v := cd.vtx ⟨1, by omega⟩) (a := cd.vtx ⟨0, by omega⟩) (b := cd.vtx ⟨2, by omega⟩)
      (e_a := cd.edge ⟨0, by omega⟩) (e_b := cd.edge ⟨1, by omega⟩) (n'' := n')
      hvVc haVc hbVc hlea hleb hends_ea₁ hends_eb₁ heab hleG hsplitG hends_Gv₁ hne_Gv₁
      hVone hVcard hLI (hgp_seed _ _ hba.symm) hgate hρ₀e₀ ?_ (ιb := _) (w := w) hwcard hw ?_ hdef
    · rw [← hcongr]; exact hρ₀Gv
    · intro j
      rcases hwmem' j with hgen | hcand
      · exact Or.inl (by rw [← hcongr]; exact hgen)
      · exact Or.inr hcand

/-- **Case III for a chain** (`lem:case-III-chain-dispatch`; from the proof of KT Lemma 6.13,
pp. 692–698): under the hypotheses of `chainData_fire_discriminator`
(`lem:case-III-chain-discriminator`), `G` has a generic full-rank realization.

The proof, as in the proof of `lem:case-III-chain-dispatch`. `chainData_fire_discriminator` gives
the normals, the form `ρ₀`, the bottom rows, the combination and the index `i` of the chosen panel.
For `2 ≤ i`, so that `d ≥ 3`, `chainData_dispatch_interior_of_discriminator` builds `(G, p_i)` from
`(G_i, q_i)`; for `i ≤ 1`, `chainData_dispatch_floor_of_discriminator` builds `(G, p_0)` or
`(G, p_1)`, both for `G` of deficiency `0` (`hG.1`). The proof of `lem:case-III`
(`case_III_realization_all_k`) applies it with `hdef_Gab` and `hsplitGP` from
`case_III_hsplit_producer_all_k`. -/
theorem PanelHingeFramework.chainData_dispatch [Infinite K]
    [DecidableEq β] [Finite α] [Finite β]
    {G : Graph α β} {n : ℕ} (cd : G.ChainData n) (hd2 : 2 ≤ cd.d) (hk1 : 1 ≤ k)
    (hn : Graph.bodyBarDim n = screwDim k)
    (hG : G.IsMinimalKDof n 0) (hV3 : 3 ≤ V(G).ncard) (hSimple : G.Simple)
    (hIH : ∀ (k' : ℤ) (G' : Graph α β), G'.IsMinimalKDof n k' → V(G').Nonempty →
      V(G').ncard < V(G).ncard →
      (G'.Simple → PanelHingeFramework.HasGenericFullRankRealization K k n G') ∧
        HasPanelRealization K k n G')
    (hdef_Gab : (G.splitOff (cd.vtx ⟨1, by omega⟩) (cd.vtx ⟨0, by omega⟩)
      (cd.vtx ⟨2, by omega⟩) cd.e₀).deficiency n = 0)
    (hsplitGP : PanelHingeFramework.HasGenericFullRankRealization K k n
      (G.splitOff (cd.vtx ⟨1, by omega⟩) (cd.vtx ⟨0, by omega⟩) (cd.vtx ⟨2, by omega⟩) cd.e₀)) :
    PanelHingeFramework.HasGenericFullRankRealization K k n G := by
  obtain ⟨q, ends, ρ₀, w, lamAB, rab, i, n', hgp, hends', -, hρ₀e₀, hw, hwmem',
      hrab, hρ₀sum, hedgeGv, hLI, hgate, hρ₀Gv⟩ :=
    PanelHingeFramework.chainData_fire_discriminator cd hd2 hk1 hn hG hV3 hSimple hIH hdef_Gab
      hsplitGP
  by_cases hint : 2 ≤ (i : ℕ)
  · have h3 : 3 ≤ cd.d := by have := i.isLt; omega
    -- `hends'` up to order, as `chainData_dispatch_interior_of_discriminator` takes it.
    exact PanelHingeFramework.chainData_dispatch_interior_of_discriminator cd h3 hSimple i hint
      hgp hρ₀e₀ hw hwmem' hedgeGv hLI hgate hρ₀Gv
      (fun _ _ _ hl => (hends'.eq_or_swap hl).imp (fun h => Prod.ext h.1 h.2)
        (fun h => Prod.ext h.1 h.2)) hG.1
  · have h1i : (i : ℕ) ≤ 1 := by omega
    exact PanelHingeFramework.chainData_dispatch_floor_of_discriminator cd hd2 hSimple i h1i
      hgp hends' hρ₀e₀ hw hwmem' hLI hgate hρ₀Gv hG.1

/-! ## Case III (`lem:case-III`) -/

/-- **Case III** (`lem:case-III`; KT Lemma 6.13, p. 692): let `K` be infinite and
`D = bodyBarDim n = screwDim k ≥ 3` (`hD`, `hn`) with `1 ≤ k`, and let `G` be a simple minimal
`0`-dof-graph with `|V(G)| ≥ 3`, no proper rigid subgraph and an edge label outside `E(G)`
(`hfresh`). Suppose that for every `k'`, every minimal `k'`-dof-graph with at least one and fewer
than `|V(G)|` vertices has a panel realization, and a generic full-rank realization if it is simple
(`hIH`). Then `G` has a generic full-rank realization. The induction of KT Theorem 5.5 uses it
(`theorem_55_minimalKDof_k_all_k`).

The proof, as in the proof of `lem:case-III`: `case_III_hsplit_producer_all_k`, with `hIH` at
`k' = 0`, realizes the triangle and the cycles and gives a chain of length `d`, from which
`chainData_dispatch` (`lem:case-III-chain-dispatch`) gives the realization. The case `d = 3` is
`k = 2`. -/
theorem PanelHingeFramework.case_III_realization_all_k
    [Infinite K] [DecidableEq β] [Finite α] [Finite β]
    {n : ℕ} (hk1 : 1 ≤ k) (hD : 3 ≤ Graph.bodyBarDim n)
    (hn : Graph.bodyBarDim n = screwDim k)
    (G : Graph α β) (hfresh : ∃ e₀ : β, e₀ ∉ E(G))
    (hG : G.IsMinimalKDof n 0) (hV3 : 3 ≤ V(G).ncard)
    (hnoRigid : ∀ H : Graph α β, ¬ H.IsProperRigidSubgraph G n)
    (hSimple : G.Simple)
    -- The induction hypothesis at every `k'`, as in `case_II_realization_all_k`.
    (hIH : ∀ (k' : ℤ) (G' : Graph α β), G'.IsMinimalKDof n k' → V(G').Nonempty →
      V(G').ncard < V(G).ncard →
      (G'.Simple → PanelHingeFramework.HasGenericFullRankRealization K k n G') ∧
        HasPanelRealization K k n G') :
    PanelHingeFramework.HasGenericFullRankRealization K k n G :=
  -- `hIH` at `k' = 0`, as `case_III_hsplit_producer_all_k` takes it, and its `hcand` from
  -- `chainData_dispatch`: `cd`, `hd2`, `hdef_Gab` and `hsplitGP` from the chain, `hk1`, `hn`, `hG`,
  -- `hV3`, `hSimple` and `hIH` from here.
  PanelHingeFramework.case_III_hsplit_producer_all_k hD hn G hG hV3 hnoRigid hSimple
    (fun G' hG' hV2 hlt =>
      hIH 0 G' hG' ((Set.ncard_pos (Set.toFinite _)).mp (by omega)) hlt)
    hfresh
    (fun cd hd2 hdef_Gab hsplitGP =>
      PanelHingeFramework.chainData_dispatch cd hd2 hk1 hn hG hV3 hSimple hIH hdef_Gab hsplitGP)

end CombinatorialRigidity.Molecular
