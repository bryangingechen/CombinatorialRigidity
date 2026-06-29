/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.AlgebraicInduction.CaseIII.Relabel.ForkedArm

/-!
# The algebraic induction — Case III realization (dispatch + capstone)

Phase 22 (molecular-conjecture program). The terminal layer of the Case-III block (`CaseIII/`
subdirectory; the post-Phase-22l molecular split round, `notes/Phase22l-perf.md`). The M₁/M₂/M₃
candidate dispatch `case_III_candidate_dispatch` (W10) discharging the `hcand` obligation via the
three arm closers (`CaseIII/Arms`, `CaseIII/Relabel`), the eq. (6.22) nested-IH rank bound
`case_III_nested_rank_lower`, and the all-`k` Case-III composer `case_III_realization` — the
capstone consumed by `AlgebraicInduction/Theorem55`.

See `ROADMAP.md` §22 and the `sec:molecular-algebraic-induction-caseIII` dep-graph in
`blueprint/src/chapter/algebraic-induction/case-iii.tex`.
-/

namespace CombinatorialRigidity.Molecular

variable {k : ℕ}

open scoped Graph

variable {α β : Type*}

/-! ## The discharge dispatch and the final Case III realization

The M₁/M₂/M₃ dispatch discharging the candidate obligation `hcand` (W10), the eq. (6.22) nested-IH
rank bound (`lem:case-III-nested-rank-lower`), and the all-`k` capstone `case_III_realization`
(`lem:case-III`). -/

/-- **W10a — the ends-congruence pre-brick** (design §1.53(b); Phase 22h). Two free-normal panel
frameworks on the *same* graph `G` and seed `q` whose endpoint selectors `ends`, `ends'` agree on
every link of `G` have *equal* rigidity-row sets. The dispatch lemma (W10b) builds the `M₁`/`M₂`
arm selector `ends₁` by overriding `Q.ends` at the two re-inserted hinges `e_a`, `e_b`; this brick
rewrites the W6b outputs (stated at `Q.ends`) into the `ends₁`-row span those arms consume.

Both `rigidityRows` sets quantify over links `G.IsLink e u v` and read `ends` only through the
support extensor `panelSupportExtensor (q ((ends e).1, ·)) (q ((ends e).2, ·))` (via
`toBodyHinge_supportExtensor` + `ofNormals_ends`/`ofNormals_normal`); the generator
`hingeRow u v r` is itself `ends`-free. So on links the support extensor — hence the hinge-row
block `(span C)^⊥` — coincides between the two frameworks, and the row sets are equal. Graph-free
over the carrier (no `whnf`; the established eval-lemma discipline, TACTICS-QUIRKS §38). No `\lean`
pin (internal infra). -/
theorem PanelHingeFramework.rigidityRows_ofNormals_congr_ends
    {G : Graph α β} {ends ends' : β → α × α} (q : α × Fin (k + 2) → ℝ)
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

/-- **W10a, swap-tolerant** (`notes/Phase23-design.md` §(4.102) Probe (c); Phase 23f). The variant
of `rigidityRows_ofNormals_congr_ends` that only requires the two endpoint selectors to record each
link of `G` *up to order* — `ends e = (u,v) ∨ (v,u)` and likewise `ends' e` — rather than agree
exactly. The two rigidity-row sets are still equal.

This is the reconcile the §(4.102) `hwmem` bottom slot needs: the general-`d` bottom-row producer
`chainData_bottom_relabel` lands at the relabel-image selector `candidateEnds i ends₀` (pinned by
its transport's `hsupp`, `ofNormals_supportExtensor_relabel_perm` — NOT re-targetable to the honest
`ends₀`), while the engine framework runs at the override `endsσρ₁`; the two record each `Gv`-link
only *up to order* (the IH's free orientation, LEAF-1 + `hends_Gv`), not exactly. Since the support
extensor at `e` reads `ends` only through `panelSupportExtensor (q (ends e).1) (q (ends e).2)`, and
swapping its two columns merely negates it (`panelSupportExtensor_swap`), the two frameworks'
support extensors at each link are `±` multiples, so `span {supportExtensor e}` — hence the
hinge-row block `(span {·})^⊥` — coincides, and the row sets are equal. Below the C.0–C.6 contract +
0-dof motive; no `\lean` pin (internal infra). -/
theorem PanelHingeFramework.rigidityRows_ofNormals_congr_ends_swap
    {G : Graph α β} {ends ends' : β → α × α} (q : α × Fin (k + 2) → ℝ)
    (hagree : ∀ e u v, G.IsLink e u v →
      (ends e = (u, v) ∨ ends e = (v, u)) ∧ (ends' e = (u, v) ∨ ends' e = (v, u))) :
    (PanelHingeFramework.ofNormals G ends q).toBodyHinge.rigidityRows
      = (PanelHingeFramework.ofNormals G ends' q).toBodyHinge.rigidityRows := by
  -- On any link `e u v`, the support extensor of either framework is `±panelSupportExtensor (q u)
  -- (q v)` (each `ends`/`ends'` recording branch collapses through `panelSupportExtensor_swap`), so
  -- both single-element spans equal `span {panelSupportExtensor (q u) (q v)}`.
  have hspan : ∀ (sel : β → α × α), (∀ e u v, G.IsLink e u v →
        sel e = (u, v) ∨ sel e = (v, u)) → ∀ e u v, G.IsLink e u v →
      Submodule.span ℝ {(PanelHingeFramework.ofNormals G sel q).toBodyHinge.supportExtensor e}
        = Submodule.span ℝ {panelSupportExtensor (fun i => q (u, i)) (fun i => q (v, i))} := by
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
    rw [BodyHingeFramework.hingeRowBlock, BodyHingeFramework.hingeRowBlock,
      hspan ends (fun e u v h => (hagree e u v h).1) e u v hlink,
      hspan ends' (fun e u v h => (hagree e u v h).2) e u v hlink]
  apply Set.eq_of_subset_of_subset
  · rintro φ ⟨e, u, v, hlink, r, hr, rfl⟩
    refine ⟨e, u, v, hlink, r, ?_, rfl⟩
    rwa [← hblock e u v hlink]
  · rintro φ ⟨e, u, v, hlink, r, hr, rfl⟩
    refine ⟨e, u, v, hlink, r, ?_, rfl⟩
    rwa [hblock e u v hlink]

/-- **Normals linear independence from algebraic independence** (§1.48(2), the LI-normals bridge;
Phase 22h base, Phase 23a general-`k` lift). For `k + 1` distinct bodies `b : Fin (k+1) → α`
(injective) in an algebraically-independent-over-`ℚ` family `q : α × Fin (k+2) → ℝ`, the `k + 1`
normal row vectors `fun i j => q (b i, j)` are `ℝ`-linearly independent.

This is the bridge the spine's reduction cases need: the IH carries
`AlgebraicIndependent ℚ (fun p => Q.normal p.1 p.2)`, and the placement uses `k + 1` distinct
normals as input to the panel-incidence discriminator (KT Case III) / the degree-`(k)` cut arm
(KT Lemma 6.5). General position (`IsGeneralPosition Q`, pairwise LI, §1.41(2)) gives the pairwise
data; this lemma provides the full `(k+1)`-tuple LI.

**Proof route** (det-polynomial, §1.48(2)): form the `(k+1)×(k+1)` submatrix
`B i j = q (b i, Fin.castSucc j)` (first `k + 1` coordinates of each row). Show `B.det ≠ 0` by:
(i) `B = (aeval (q ∘ f)).mapMatrix (mvPolynomialX (Fin (k+1)) (Fin (k+1)) ℚ)`
    where `f (i,j) = (b i, Fin.castSucc j)` (by `mvPolynomialX_mapMatrix_aeval`);
(ii) `B.det = aeval (q ∘ f) (det (mvPolynomialX ...))` (by `AlgHom.map_det`);
(iii) `det (mvPolynomialX (Fin (k+1)) (Fin (k+1)) ℚ) ≠ 0` (`Matrix.det_mvPolynomialX_ne_zero`);
(iv) `q ∘ f` is alg-indep over ℚ (`AlgebraicIndependent.comp`, since `f` is injective by `b`
     injective and `Fin.castSucc` injective);
(v) `AlgebraicIndependent.aeval_ne_zero` certifies `B.det ≠ 0`.
Then `Matrix.linearIndependent_rows_of_det_ne_zero` + `LinearIndependent.of_comp` (projection to
first `k + 1` coordinates) lifts to the full `(k+2)`-coordinate rows. No `d = 3` content: the same
Vandermonde/projection argument runs at every grade. -/
lemma linearIndependent_normals_of_algebraicIndependent_general
    {k : ℕ} {α : Type*} {q : α × Fin (k + 2) → ℝ}
    (hq : AlgebraicIndependent ℚ q)
    {b : Fin (k + 1) → α} (hb : Function.Injective b) :
    LinearIndependent ℝ (fun (i : Fin (k + 1)) (j : Fin (k + 2)) => q (b i, j)) := by
  classical
  -- Suffices: the projection to the first `k + 1` coordinates is also independent.
  -- If the full-row family is dependent, so is the projected family; so we prove LI of the
  -- projected family (rows of the (k+1)×(k+1) matrix B) and lift back.
  apply LinearIndependent.of_comp
    (LinearMap.pi (fun j : Fin (k + 1) =>
      (LinearMap.proj (Fin.castSucc j) : (Fin (k + 2) → ℝ) →ₗ[ℝ] ℝ)))
  -- The composed family equals the rows of the matrix B i j = q (b i, Fin.castSucc j).
  have hcomp_eq : (LinearMap.pi
        (fun j : Fin (k + 1) =>
          (LinearMap.proj (Fin.castSucc j) : (Fin (k + 2) → ℝ) →ₗ[ℝ] ℝ))) ∘
      (fun (i : Fin (k + 1)) (j : Fin (k + 2)) => q (b i, j)) =
      fun (i : Fin (k + 1)) (j : Fin (k + 1)) => q (b i, Fin.castSucc j) := rfl
  rw [hcomp_eq]
  -- Show the matrix B has nonzero determinant (rows are then linearly independent).
  apply Matrix.linearIndependent_rows_of_det_ne_zero
  -- Set up the injection f : Fin (k+1) × Fin (k+1) → α × Fin (k+2).
  set f : Fin (k + 1) × Fin (k + 1) → α × Fin (k + 2) :=
    fun p => (b p.1, Fin.castSucc p.2) with hf_def
  have hfinj : Function.Injective f := by
    intro ⟨i, j⟩ ⟨i', j'⟩ heq
    simp only [hf_def, Prod.mk.injEq] at heq
    exact Prod.ext (hb heq.1) (Fin.castSucc_injective _ heq.2)
  -- q∘f is algebraically independent over ℚ (injective precomposition of an alg-indep family).
  have hqf : AlgebraicIndependent ℚ (q ∘ f) := hq.comp f hfinj
  -- The generic (k+1)×(k+1) det polynomial P = det(mvPolynomialX) is nonzero over ℚ.
  have hP_ne : (Matrix.mvPolynomialX (Fin (k + 1)) (Fin (k + 1)) ℚ).det ≠ 0 :=
    Matrix.det_mvPolynomialX_ne_zero (Fin (k + 1)) ℚ
  -- B.det = aeval(q∘f) P.  Use mvPolynomialX_mapMatrix_aeval: aeval(A.·) (mvPolynomialX) = A,
  -- then take .det and apply AlgHom.map_det.
  suffices hBdet :
      Matrix.det (fun i j => q (b i, Fin.castSucc j)) =
      MvPolynomial.aeval (fun p : Fin (k + 1) × Fin (k + 1) => (q ∘ f) p)
        (Matrix.mvPolynomialX (Fin (k + 1)) (Fin (k + 1)) ℚ).det by
    rw [hBdet]
    exact hqf.aeval_ne_zero hP_ne
  -- Prove B.det = aeval(q∘f) det(mvPolynomialX).
  -- Step 1: (aeval (fun p => (q∘f) p)).mapMatrix (mvPolynomialX) = B
  --         (by mvPolynomialX_mapMatrix_aeval, since (q∘f) p = B p.1 p.2 definitionally).
  have hφB : (MvPolynomial.aeval (fun p : Fin (k + 1) × Fin (k + 1) => (q ∘ f) p)).mapMatrix
      (Matrix.mvPolynomialX (Fin (k + 1)) (Fin (k + 1)) ℚ) =
      (fun i j => q (b i, Fin.castSucc j)) := by
    have := Matrix.mvPolynomialX_mapMatrix_aeval ℚ
      (Matrix.of (fun i j : Fin (k + 1) => q (b i, Fin.castSucc j)))
    simp only [Matrix.of_apply] at this
    convert this using 2
  -- Step 2: aeval(q∘f) (det mvPolynomialX) = (aeval(q∘f).mapMatrix (mvPolynomialX)).det
  --         by AlgHom.map_det (reversed direction).
  rw [← hφB, AlgHom.map_det]

/-- **Triple linear independence from algebraic independence — general grade** (§1.48(2), the
triple-LI bridge; Phase 22h base, Phase 23b general-`k` lift, OD-7 `hcontract_k` LEAF-0). For three
distinct vertices `a, b, c` in an algebraically-independent-over-`ℚ` family `q : α × Fin (k+2) → ℝ`
(grade `k ≥ 1`, so the rows live in a `≥ 3`-dimensional column space), the three row vectors
`![q(a,·), q(b,·), q(c,·)]` are `ℝ`-linearly independent.

This is the **genuinely-new** brick of the Case-I dispatch lift (unlike the `_general` companion,
which produces LI of a `k + 1`-row family from `k + 1` injective vertices): the KT Lemma 6.5 arm
(`case_I_realization_h65`) has only a degree-2 vertex `v` plus its two neighbours `a, b` — three
vertices, not `k + 1` — so for `k ≥ 3` the `k + 1`-vertex selector of `_general` is unavailable and
the *fixed-three-row* statement needs its own proof. (The `d = 3`, i.e. `k = 2`, instance below is
where the row count `3` happens to coincide with `k + 1`.)

**Proof route** (det-polynomial, the `_general` argument restricted to a fixed `3 × 3` minor):
project the `k + 2` columns onto the first three via `Fin.castLE (by omega : 3 ≤ k + 2)`, form the
`3 × 3` matrix `B i j = q (![a,b,c] i, Fin.castLE … j)`, and show `B.det ≠ 0` by
`AlgebraicIndependent.aeval_ne_zero` applied to the generic `det (mvPolynomialX (Fin 3) (Fin 3) ℚ)`
(nonzero by `Matrix.det_mvPolynomialX_ne_zero`) along the injection
`f (i, j) = (![a,b,c] i, Fin.castLE … j)` (injective: `![a,b,c]` from the three distinctnesses,
`Fin.castLE` from `Fin.castLE_injective`). Then `Matrix.linearIndependent_rows_of_det_ne_zero` plus
`LinearIndependent.of_comp` lift the `3 × 3`-minor independence to the full `(k+2)`-coordinate rows.
No `d = 3` content; only `k ≥ 1` (the column space must be at least three-dimensional). -/
lemma linearIndependent_normals_of_algebraicIndependent_triple
    {k : ℕ} {α : Type*} (hk : 1 ≤ k) {q : α × Fin (k + 2) → ℝ}
    (hq : AlgebraicIndependent ℚ q)
    {a b c : α} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    LinearIndependent ℝ (![fun i => q (a, i), fun i => q (b, i), fun i => q (c, i)] :
      Fin 3 → Fin (k + 2) → ℝ) := by
  classical
  have h3 : (3 : ℕ) ≤ k + 2 := by omega
  have hbinj : Function.Injective (![a, b, c] : Fin 3 → α) := by
    intro i j heq
    fin_cases i <;> fin_cases j <;>
      simp_all [Matrix.cons_val_zero, Matrix.cons_val_one, hab.symm, hac.symm, hbc.symm]
  -- It suffices that the projection to three columns `Fin.castLE h3 : Fin 3 → Fin (k+2)` is LI.
  -- The literal row family equals the selector family `fun i j => q (![a,b,c] i, j)`.
  have hrows : (![fun i => q (a, i), fun i => q (b, i), fun i => q (c, i)] :
        Fin 3 → Fin (k + 2) → ℝ) =
      fun (i : Fin 3) (j : Fin (k + 2)) => q (![a, b, c] i, j) := by
    ext i j; fin_cases i <;> rfl
  rw [hrows]
  apply LinearIndependent.of_comp
    (LinearMap.pi (fun j : Fin 3 =>
      (LinearMap.proj (Fin.castLE h3 j) : (Fin (k + 2) → ℝ) →ₗ[ℝ] ℝ)))
  -- The composed family is the rows of the 3×3 matrix B i j = q (![a,b,c] i, Fin.castLE h3 j).
  have hcomp_eq : (LinearMap.pi
        (fun j : Fin 3 =>
          (LinearMap.proj (Fin.castLE h3 j) : (Fin (k + 2) → ℝ) →ₗ[ℝ] ℝ))) ∘
      (fun (i : Fin 3) (j : Fin (k + 2)) => q (![a, b, c] i, j)) =
      fun (i : Fin 3) (j : Fin 3) => q (![a, b, c] i, Fin.castLE h3 j) := rfl
  rw [hcomp_eq]
  apply Matrix.linearIndependent_rows_of_det_ne_zero
  -- Injection f : Fin 3 × Fin 3 → α × Fin (k+2) selecting the three rows and three columns.
  set f : Fin 3 × Fin 3 → α × Fin (k + 2) :=
    fun p => (![a, b, c] p.1, Fin.castLE h3 p.2) with hf_def
  have hfinj : Function.Injective f := by
    intro ⟨i, j⟩ ⟨i', j'⟩ heq
    simp only [hf_def, Prod.mk.injEq] at heq
    exact Prod.ext (hbinj heq.1) (Fin.castLE_injective h3 heq.2)
  have hqf : AlgebraicIndependent ℚ (q ∘ f) := hq.comp f hfinj
  have hP_ne : (Matrix.mvPolynomialX (Fin 3) (Fin 3) ℚ).det ≠ 0 :=
    Matrix.det_mvPolynomialX_ne_zero (Fin 3) ℚ
  suffices hBdet :
      Matrix.det (fun i j => q (![a, b, c] i, Fin.castLE h3 j)) =
      MvPolynomial.aeval (fun p : Fin 3 × Fin 3 => (q ∘ f) p)
        (Matrix.mvPolynomialX (Fin 3) (Fin 3) ℚ).det by
    rw [hBdet]
    exact hqf.aeval_ne_zero hP_ne
  have hφB : (MvPolynomial.aeval (fun p : Fin 3 × Fin 3 => (q ∘ f) p)).mapMatrix
      (Matrix.mvPolynomialX (Fin 3) (Fin 3) ℚ) =
      (fun i j => q (![a, b, c] i, Fin.castLE h3 j)) := by
    have := Matrix.mvPolynomialX_mapMatrix_aeval ℚ
      (Matrix.of (fun i j : Fin 3 => q (![a, b, c] i, Fin.castLE h3 j)))
    simp only [Matrix.of_apply] at this
    convert this using 2
  rw [← hφB, AlgHom.map_det]

/-- **Triple linear independence from algebraic independence** (§1.48(2), the triple-LI bridge;
Phase 22h). For three distinct vertices `a, b, c` in an algebraically-independent-over-`ℚ` family
`q : α × Fin 4 → ℝ`, the three row vectors `![q(a,·), q(b,·), q(c,·)]` are `ℝ`-linearly
independent. The `d = 3` (`k = 2`) instance of
`linearIndependent_normals_of_algebraicIndependent_triple`; kept at the `![…]` literal `Fin 4`
signature for the still-`k = 2` spine consumers (`case_III_candidate_dispatch`,
`case_I_realization_h65`). -/
lemma linearIndependent_normals_of_algebraicIndependent
    {α : Type*} {q : α × Fin 4 → ℝ}
    (hq : AlgebraicIndependent ℚ q)
    {a b c : α} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    LinearIndependent ℝ (![fun i => q (a, i), fun i => q (b, i), fun i => q (c, i)] :
      Fin 3 → Fin 4 → ℝ) :=
  linearIndependent_normals_of_algebraicIndependent_triple (k := 2) (by norm_num) hq hab hac hbc

/-- **W10b — the candidate-placement dispatch + discharge assembly** (`lem:case-II-realization` /
`lem:case-III`, the `hcand` discharge of the `d = 3` `hsplit` producer; Katoh–Tanigawa 2011
§6.4.1, eqs.~(6.24)–(6.44), design §1.53(c)/(d), Phase 22h). This is the assembly that matches the
producer's `hcand` parameter shape (`case_III_hsplit_producer`) and discharges it: from the chain
data, a fresh `e₀`, and the IH-derived **generic** `v`-split realization `hsplitGP`, it produces
the generic realization of `G`.

The route (KT p. 686): one invocation of the W6b packaging
(`exists_candidateRow_bottomRows_of_rigidOn`) at the `v`-split extracts the candidate functional
`ρ`, its annihilation `ρ(C(e₀)) = 0`, its span membership, and the bottom family `w` — *one*
redundancy, *one* GAP-6 consumption (carried as `h622lb`, instantiated at the IH seed/selector
`(Q.ends, q)`). After normalizing the W6b outputs to the chain order `(a, b)` (the landed W8
sign-swap pattern), the discriminator (`exists_homogeneousIncidence_of_normals` +
`exists_complementIso_ne_zero_of_homogeneousIncidence`) picks the discriminating panel `u : Fin 3`
and a transversal normal `n'` with `ρ(panelSupportExtensor (![n_a,n_b,n_c] u) n') ≠ 0`.
`fin_cases u` dispatches to the three arm closers: `u = 0 ↦` W7 (the `a`-side line `L ⊂ Π(a)`),
`u = 1 ↦` W8 (the `b`-side line, the swapped-role W7), `u = 2 ↦` W9c (the `c`-side line, the
relabel-instantiation of W7 at `G − a`). The M₁/M₂ arms consume the W6b row-set outputs at the
override selector `ends₁`; the W10a congruence pre-brick (`rigidityRows_ofNormals_congr_ends`)
rewrites the `Q.ends`-stated outputs into `ends₁`-row span those arms expect. The M₃ arm consumes
at `Q.ends` directly. No leftover obligations beyond the carried `h622lb` (never a `sorry`). -/
theorem PanelHingeFramework.case_III_candidate_dispatch
    [Finite α] [Finite β]
    (G : Graph α β) (v a b c : α) (e_a e_b e_c e₀ : β)
    (hsimple : G.Simple)
    (hvG : v ∈ V(G)) (haG : a ∈ V(G)) (hbG : b ∈ V(G)) (hcG : c ∈ V(G))
    (hav : a ≠ v) (hbv : b ≠ v) (hba : b ≠ a) (hcv : c ≠ v) (hca : c ≠ a) (hbc : b ≠ c)
    (heab : e_a ≠ e_b) (heac : e_a ≠ e_c)
    (hlea : G.IsLink e_a v a) (hleb : G.IsLink e_b v b) (hlec : G.IsLink e_c a c)
    (hclv : ∀ e x, G.IsLink e v x → e = e_a ∨ e = e_b)
    (hcla : ∀ e x, G.IsLink e a x → e = e_a ∨ e = e_c)
    (he₀ : e₀ ∉ E(G))
    -- GAP 6 (adjudicated carry, §1.50(b) option (ii)): the eq.-(6.22) nested-IH rank bound at
    -- `G − v`, quantified over the (existentially bound) IH selector/seed and conditioned on the
    -- IH-suppliable facts (§1.53(a)2). Instantiated inside the proof at `(Q.ends, q)`; fed to W6b
    -- as its `h622lb`. An explicit named hypothesis, never a `sorry`.
    (h622lb : ∀ (ends : β → α × α) (q : α × Fin 4 → ℝ),
      (∀ e u w, (G.splitOff v a b e₀).IsLink e u w → ends e = (u, w) ∨ ends e = (w, u)) →
      (∀ x y : α, x ≠ y → LinearIndependent ℝ ![fun i => q (x, i), fun i => q (y, i)]) →
      AlgebraicIndependent ℚ q →
      screwDim 2 * (V(G.splitOff v a b e₀).ncard - 1) - (screwDim 2 - 2)
        ≤ Module.finrank ℝ (Submodule.span ℝ
            (PanelHingeFramework.ofNormals (G.removeVertex v) ends
              q).toBodyHinge.rigidityRows))
    {n : ℕ} (hdef_Gab : (G.splitOff v a b e₀).deficiency n = 0)
    (hdef : G.deficiency n = 0)
    (hsplitGP : PanelHingeFramework.HasGenericFullRankRealization 2 n (G.splitOff v a b e₀)) :
    PanelHingeFramework.HasGenericFullRankRealization 2 n G := by
  classical
  haveI : Fintype α := Fintype.ofFinite α
  haveI hGloop : G.Loopless := hsimple.toLoopless
  set Gab := G.splitOff v a b e₀ with hGab
  set Gv := G.removeVertex v with hGv
  haveI : Gv.Loopless := hGloop.mono (hGv ▸ Graph.removeVertex_le G v)
  -- 1. Unpack the generic `v`-split realization; re-express `Q` as `ofNormals Gab Q.ends q`.
  obtain ⟨Q, hQg, hQgp, hQrank, hQrec, hQalg⟩ := hsplitGP
  set q : α × Fin 4 → ℝ := fun p => Q.normal p.1 p.2 with hq
  have hQeq : PanelHingeFramework.ofNormals Gab Q.ends q = Q := by rw [hq, ← hQg]; rfl
  have hgp' : (PanelHingeFramework.ofNormals Gab Q.ends q).IsGeneralPosition := by
    rw [hQeq]; exact hQgp
  have hne' : V(Gab).Nonempty := ⟨a, by rw [hGab, Graph.vertexSet_splitOff]; exact ⟨haG, by
    simp [hav]⟩⟩
  have hne_Q : Q.toBodyHinge.graph.vertexSet.Nonempty := by
    rw [PanelHingeFramework.toBodyHinge_graph, hQg]; exact hne'
  rw [hdef_Gab, sub_zero] at hQrank
  have hVeq_Gab : V(Gab) = Q.toBodyHinge.graph.vertexSet := by
    rw [PanelHingeFramework.toBodyHinge_graph, hQg]
  have h1_Gab : 1 ≤ V(Gab).ncard := (Set.ncard_pos (Set.toFinite _)).2 hne'
  have hQrig : Q.toBodyHinge.IsInfinitesimallyRigidOn V(Gab) := by
    rw [hVeq_Gab,
      BodyHingeFramework.isInfinitesimallyRigidOn_vertexSet_iff_finrank_span_rigidityRows
        Q.toBodyHinge hne_Q, ← hVeq_Gab]
    zify [h1_Gab] at hQrank ⊢; exact_mod_cast hQrank
  have hrig' : (PanelHingeFramework.ofNormals Gab Q.ends q).toBodyHinge.IsInfinitesimallyRigidOn
      V(Gab) := by rw [hQeq]; exact hQrig
  have hrec' : ∀ e u w, Gab.IsLink e u w → Q.ends e = (u, w) ∨ Q.ends e = (w, u) := by
    intro e u w he
    rcases hQrec e u w he with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl (Prod.ext h1 h2)
    · exact Or.inr (Prod.ext h1 h2)
  -- 2. Inline graph facts.
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
  have hGv_off : ∀ {e u w}, Gv.IsLink e u w → e ≠ e_a ∧ e ≠ e_b := by
    intro e u w hlink
    rw [hGv, Graph.removeVertex_isLink] at hlink
    obtain ⟨hGlink, hunev, hwnev⟩ := hlink
    refine ⟨fun he => ?_, fun he => ?_⟩
    · subst he
      rcases hlea.eq_and_eq_or_eq_and_eq hGlink with ⟨hh, _⟩ | ⟨hh, _⟩
      · exact hunev hh.symm
      · exact hwnev hh.symm
    · subst he
      rcases hleb.eq_and_eq_or_eq_and_eq hGlink with ⟨hh, _⟩ | ⟨hh, _⟩
      · exact hunev hh.symm
      · exact hwnev hh.symm
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
    rw [hGab, hGv, Graph.vertexSet_splitOff, Graph.vertexSet_removeVertex]
  have hgp_seed : ∀ x y : α, x ≠ y →
      LinearIndependent ℝ ![fun i => q (x, i), fun i => q (y, i)] := by
    intro x y hxy
    have := hgp' x y hxy
    rw [PanelHingeFramework.ofNormals_normal, PanelHingeFramework.ofNormals_normal] at this
    exact this
  -- 3. W6b: one invocation extracting the candidate / bottom data.
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
      (h622lb Q.ends q hrec' hgp_seed hQalg)
  -- 4. Normalize the W6b outputs to chain order `(a, b)` (the W8 sign-swap pattern).
  set na := (fun i => q (a, i)) with hna
  set nb := (fun i => q (b, i)) with hnb
  set nc := (fun i => q (c, i)) with hnc
  -- The `supportExtensor e₀`-form annihilation in `panelSupportExtensor` form.
  have hsupp_e₀ : ∀ (r : Module.Dual ℝ (ScrewSpace 2)),
      r ((PanelHingeFramework.ofNormals Gab Q.ends q).toBodyHinge.supportExtensor e₀) =
        r (panelSupportExtensor (fun i => q ((Q.ends e₀).1, i))
          (fun i => q ((Q.ends e₀).2, i))) := by
    intro r
    rw [PanelHingeFramework.toBodyHinge_supportExtensor, PanelHingeFramework.ofNormals_ends,
      PanelHingeFramework.ofNormals_normal, PanelHingeFramework.ofNormals_normal]
  obtain ⟨ρ0, hρ0ne, hρ0e₀, hρ0Gv, hw0mem⟩ :
      ∃ ρ0 : Module.Dual ℝ (ScrewSpace 2), ρ0 ≠ 0 ∧
        ρ0 (panelSupportExtensor na nb) = 0 ∧
        BodyHingeFramework.hingeRow a b ρ0 ∈ Submodule.span ℝ
          (PanelHingeFramework.ofNormals Gv Q.ends q).toBodyHinge.rigidityRows ∧
        (∀ j, w j ∈ (PanelHingeFramework.ofNormals Gv Q.ends q).toBodyHinge.rigidityRows ∨
          ∃ ρ' : Module.Dual ℝ (ScrewSpace 2),
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
  -- 5. The discriminator: pick the discriminating panel `u : Fin 3` and transversal normal `n'`.
  have hn : LinearIndependent ℝ ![na, nb, nc] :=
    linearIndependent_normals_of_algebraicIndependent hQalg hba.symm hca.symm hbc
  obtain ⟨pbar, hp, h0, h1, h2, h3⟩ := exists_homogeneousIncidence_of_normals hn
  obtain ⟨u, n', hpair, hgate⟩ :=
    BodyHingeFramework.exists_complementIso_ne_zero_of_homogeneousIncidence
      hρ0ne hp hn h0 ⟨h1.1, h1.2.1⟩ ⟨h2.1, h2.2.1⟩ ⟨h3.1, h3.2.1⟩
  rw [← panelSupportExtensor_eq_complementIso_extensor] at hgate
  -- The M₁/M₂ override selector `ends₁` and the M₃ override selector `ends₃`.
  set ends₁ : β → α × α := Function.update (Function.update Q.ends e_a (v, a)) e_b (v, b)
    with hends₁
  -- `ends₁` reduces to `Q.ends` off `{e_a, e_b}`, used by the W10a congruence on `Gv`-links.
  have hends₁_off : ∀ {e}, e ≠ e_a → e ≠ e_b → ends₁ e = Q.ends e := by
    intro e hea heb
    rw [hends₁, Function.update_of_ne heb, Function.update_of_ne hea]
  have hcongr : (PanelHingeFramework.ofNormals Gv Q.ends q).toBodyHinge.rigidityRows
      = (PanelHingeFramework.ofNormals Gv ends₁ q).toBodyHinge.rigidityRows :=
    PanelHingeFramework.rigidityRows_ofNormals_congr_ends q
      (fun e u w hlink => (hends₁_off (hGv_off hlink).1 (hGv_off hlink).2).symm)
  -- Common `Gv`/`G` facts shared by the M₁/M₂ arms.
  have hvVc : v ∉ V(Gv) := by rw [hGv, Graph.vertexSet_removeVertex]; exact fun h => h.2 rfl
  have haVc : a ∈ V(Gv) := by rw [hGv, Graph.vertexSet_removeVertex]; exact ⟨haG, hav⟩
  have hbVc : b ∈ V(Gv) := by rw [hGv, Graph.vertexSet_removeVertex]; exact ⟨hbG, hbv⟩
  have hleG : ∀ e u w, Gv.IsLink e u w → G.IsLink e u w := by
    intro e u w hlink; rw [hGv, Graph.removeVertex_isLink] at hlink; exact hlink.1
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
    rw [hGv, Graph.vertexSet_removeVertex, Set.ncard_diff_singleton_of_mem hvG]; omega
  have hVcard : V(G).ncard = V(Gv).ncard + 1 := by
    rw [hGv, Graph.vertexSet_removeVertex, Set.ncard_diff_singleton_of_mem hvG]; omega
  -- The M₁/M₂ arm `ends₁`-stated selector facts.
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
  -- 6. Dispatch on `u`.
  fin_cases u
  · -- `u = 0` → W7 (the `a`-side line).
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
  · -- `u = 1` → W8 (the `b`-side line).
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
  · -- `u = 2` → W9c (the `c`-side line, the relabel-instantiation at `G − a`).
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
      rw [hends₃, Function.update_of_ne hebc.symm, Function.update_of_ne heac.symm,
        Function.update_self]
    have hends₃_ea : ends₃ e_a = (a, v) := by
      rw [hends₃, Function.update_of_ne heab, Function.update_self]
    have hends₃_eb : ends₃ e_b = (v, b) := by rw [hends₃, Function.update_self]
    have hends₃_off : ∀ e, e ≠ e_a → e ≠ e_b → e ≠ e_c → ends₃ e = Q.ends e := by
      intro e hea heb hec
      rw [hends₃, Function.update_of_ne heb, Function.update_of_ne hea, Function.update_of_ne hec]
    haveI : (G.removeVertex a).Loopless := hGloop.mono (Graph.removeVertex_le G a)
    set qρ : α × Fin 4 → ℝ := fun p => q (Equiv.swap a v p.1, p.2) with hqρ
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
    have hV3 : 3 ≤ V(G).ncard := by omega
    refine PanelHingeFramework.case_III_arm_realization_M3 (k := 2) G Q.ends ends₃ (q := q)
      (v := v) (a := a) (b := b) (c := c) (e_a := e_a) (e_b := e_b) (e_c := e_c) (n''' := n')
      hav.symm hba.symm hbv.symm hca hcv hlea hleb hlec heac hcla hrecGv
      hends₃_ec hends₃_ea hends₃_eb hends₃_off hends_Gva hne_Gva hV3 hpair (hgp_seed c a hca)
      hgate hρ0e₀ hρ0Gv (ιb := _) (w := w) ?_ hw ?_ hdef
    · have hGabcard : V(Gab).ncard = V(G).ncard - 1 := by
        rw [hGab, Graph.vertexSet_splitOff, Set.ncard_diff_singleton_of_mem hvG]
      rw [Nat.card_fin, hGabcard, Nat.sub_sub]
    · intro j
      rcases hw0mem j with hgen | hcand
      · exact Or.inl hgen
      · exact Or.inr hcand

/-- **Eq.-(6.22) nested rank lower bound — all-`k` form** (`lem:case-III-nested-rank-lower`;
Katoh–Tanigawa 2011
eq.\ (6.22), nested hypothesis (6.1); Phase 22k L7b base, Phase 23a Leaf 4 general-`k` lift). For a
simple minimal `0`-dof-graph `G` with a
degree-2 vertex `v` (its two `v`-edges are `eₐ : v—a`, `e_b : v—b`, and no others) and a fresh edge
`e₀ ∉ E(G)`, the free-normal panel framework on the vertex-removal `Gv = G − v` attains, at any
link-recording selector and any pairwise-LI, algebraically-independent seed, at least the rank
`D(|V(G.splitOff v a b e₀)| − 1) − (D − 2)` that KT's hypothesis (6.1) predicts.

This is KT's *nested* use of the induction (Claim 6.11, eq. (6.22)), discharged from the **all-`k`
IH** — not the `0`-dof-only motive: the nested subgraph `Gv` is minimal `k'`-dof with `k' ≤ D − 2`
(`splitOff_removeVertex_minimalKDof`), so the IH realizes it at rank `D(|Vᵥ| − 1) − k'`, and the
landed L7a rank-polynomial extractor (`exists_rankPolynomial_of_IH_linking`) plus the footnote-6
non-root device transfer that rank to the given seed; `k' ≤ D − 2` closes the arithmetic. The bound
holds at `|V(Gᵃᵇ)| = |V(G)| − 1 ≥ 2` (from `hV3`), so it needs no fourth vertex. -/
theorem PanelHingeFramework.case_III_nested_rank_lower_all_k
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
      (G'.Simple → PanelHingeFramework.HasGenericFullRankRealization k n G') ∧
        HasPanelRealization k n G') :
    ∀ (ends : β → α × α) (q : α × Fin (k + 2) → ℝ),
      (∀ e u w, (G.splitOff v a b e₀).IsLink e u w → ends e = (u, w) ∨ ends e = (w, u)) →
      (∀ x y : α, x ≠ y → LinearIndependent ℝ ![fun i => q (x, i), fun i => q (y, i)]) →
      AlgebraicIndependent ℚ q →
      screwDim k * (V(G.splitOff v a b e₀).ncard - 1) - (screwDim k - 2)
        ≤ Module.finrank ℝ (Submodule.span ℝ
            (PanelHingeFramework.ofNormals (G.removeVertex v) ends
              q).toBodyHinge.rigidityRows) := by
  intro ends q hrecEnds _hgp_seed hQalg
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
  -- `Graph.splitOff_removeVertex_minimalKDof`: `G.removeVertex v` is minimal `k'`-dof
  -- with `k' ≤ D−2`.
  obtain ⟨hGvmin, _hk'nn, hk'le⟩ :=
    Graph.splitOff_removeVertex_minimalKDof (by omega : 2 ≤ Graph.bodyBarDim n)
      hba.symm hav hbv heab hlea hleb hclv he₀ hG
  -- `G.removeVertex v` is simple, nonempty, and strictly smaller than `G`.
  have hGvSimple : (G.removeVertex v).Simple := hSimple.mono (Graph.removeVertex_le G v)
  have hGvne : V(G.removeVertex v).Nonempty :=
    ⟨a, by rw [Graph.vertexSet_removeVertex]; exact ⟨hlea.right_mem, hav⟩⟩
  have hGvlt : V(G.removeVertex v).ncard < V(G).ncard := by
    rw [Graph.vertexSet_removeVertex,
      Set.ncard_diff_singleton_of_mem (hlea.left_mem : v ∈ V(G))]; omega
  -- All-`k` IH at `G.removeVertex v`.
  have hQv : PanelHingeFramework.HasGenericFullRankRealization k n (G.removeVertex v) :=
    (hIH _ (G.removeVertex v) hGvmin hGvne hGvlt).1 hGvSimple
  haveI hGvloop : (G.removeVertex v).Loopless := hGvSimple.toLoopless
  -- L7a: extract rank polynomial `P` with rational coefficients.
  obtain ⟨N, hNeq, P, hPne, hPrat, hPtrans⟩ :=
    PanelHingeFramework.exists_rankPolynomial_of_IH_linking (G.removeVertex v) ends hQv
      hGvloop hends'
  -- Footnote-6: `q` (algebraically independent) is not a root of the nonzero rational `P`.
  have hPeval : MvPolynomial.eval q P ≠ 0 :=
    MvPolynomial.eval_ne_zero_of_coeffs_subset_range_of_algebraicIndependent hQalg hPrat hPne
  -- `N ≤ finrank`.
  have hNle : N ≤ Module.finrank ℝ (Submodule.span ℝ
      (PanelHingeFramework.ofNormals (G.removeVertex v) ends q).toBodyHinge.rigidityRows) :=
    hPtrans q hPeval
  -- Arithmetic: `D(|Gab|−1)−(D−2) ≤ N ≤ finrank`. With `|Gab| = |Gv|` (hcard), `k' ≤ D−2`
  -- (hk'le), `hn : D = screwDim k`, and `N = D(|Gv|−1) − k'` (hNeq):
  -- `D(|Gab|−1) − (D−2) = D(|Gv|−1) − (D−2) ≤ D(|Gv|−1) − k' = N`. The two `screwDim 2`-only
  -- `decide` facts the `d = 3` proof used are now Leaf-0 kit calls (`two_le_screwDim`,
  -- `screwDim_sub_two_le_mul`).
  have hGvne1 : 1 ≤ V(G.splitOff v a b e₀).ncard :=
    hcard ▸ (Set.ncard_pos (Set.toFinite _)).2 hGvne
  have hDge2 : 2 ≤ screwDim k := two_le_screwDim hk1
  -- `|Gab| = |Gv| = |V(G)| − 1 ≥ 2` (one vertex `v` removed from `|V(G)| ≥ 3`).
  have hGab2 : 2 ≤ V(G.splitOff v a b e₀).ncard := by
    rw [hcard, Graph.vertexSet_removeVertex,
      Set.ncard_diff_singleton_of_mem (hlea.left_mem : v ∈ V(G))]; omega
  have hcardZ : (V(G.splitOff v a b e₀).ncard : ℤ) = V(G.removeVertex v).ncard := by
    exact_mod_cast hcard
  have hD_eq : (screwDim k : ℤ) = Graph.bodyBarDim n := by omega
  -- `LHS ≤ N` (ℕ): with `|Gab| ≥ 2` the ℕ-subtractions are safe; compare via ℤ.
  have hDsub : screwDim k - 2 ≤ screwDim k * (V(G.splitOff v a b e₀).ncard - 1) :=
    screwDim_sub_two_le_mul hGab2
  have hLHSN : screwDim k * (V(G.splitOff v a b e₀).ncard - 1) - (screwDim k - 2) ≤ N := by
    apply Nat.cast_le (α := ℤ) |>.mp
    rw [Nat.cast_sub hDsub, Nat.cast_mul, Nat.cast_sub hGvne1, Nat.cast_sub hDge2]
    simp only [Nat.cast_one, Nat.cast_ofNat]
    rw [← hcardZ] at hNeq
    linarith [hNeq, hk'le, hD_eq]
  exact le_trans hLHSN hNle

/-- **Eq.-(6.22) nested rank lower bound, `d = 3`** (`lem:case-III-nested-rank-lower`; the `k = 2`
specialization of `case_III_nested_rank_lower_all_k`, Phase 23a Leaf 4). Thin wrapper at
`Fin 4`/`screwDim 2`/`HasGenericFullRankRealization 2`, discharging the `1 ≤ k` floor at `2` by
`norm_num`; the `d = 3` candidate dispatch's `h622lb` slot consumes this shape. -/
theorem PanelHingeFramework.case_III_nested_rank_lower [DecidableEq β] [Finite α] [Finite β]
    {n : ℕ} (hn : Graph.bodyBarDim n = screwDim 2)
    (G : Graph α β) (v a b : α) (eₐ e_b e₀ : β)
    (hG : G.IsMinimalKDof n 0) (hV3 : 3 ≤ V(G).ncard) (hSimple : G.Simple)
    (hba : b ≠ a) (hav : a ≠ v) (hbv : b ≠ v) (heab : eₐ ≠ e_b)
    (hlea : G.IsLink eₐ v a) (hleb : G.IsLink e_b v b)
    (hclv : ∀ e x, G.IsLink e v x → e = eₐ ∨ e = e_b)
    (he₀ : e₀ ∉ E(G))
    (hIH : ∀ (k' : ℤ) (G' : Graph α β), G'.IsMinimalKDof n k' → V(G').Nonempty →
      V(G').ncard < V(G).ncard →
      (G'.Simple → PanelHingeFramework.HasGenericFullRankRealization 2 n G') ∧
        HasPanelRealization 2 n G') :
    ∀ (ends : β → α × α) (q : α × Fin 4 → ℝ),
      (∀ e u w, (G.splitOff v a b e₀).IsLink e u w → ends e = (u, w) ∨ ends e = (w, u)) →
      (∀ x y : α, x ≠ y → LinearIndependent ℝ ![fun i => q (x, i), fun i => q (y, i)]) →
      AlgebraicIndependent ℚ q →
      screwDim 2 * (V(G.splitOff v a b e₀).ncard - 1) - (screwDim 2 - 2)
        ≤ Module.finrank ℝ (Submodule.span ℝ
            (PanelHingeFramework.ofNormals (G.removeVertex v) ends
              q).toBodyHinge.rigidityRows) :=
  PanelHingeFramework.case_III_nested_rank_lower_all_k (k := 2) (by norm_num) hn G v a b eₐ e_b e₀
    hG hV3 hSimple hba hav hbv heab hlea hleb hclv he₀ hIH

/-- **CHAIN-2c-iii D1 — the interior split-off's IH-fed generic realization** (`lem:case-III`
general-`d`; Katoh–Tanigawa 2011 §6.4.2, Lemma 6.13; Phase 23f). From the all-`k` IH (the `0`-dof
motive's induction hypothesis the Case-III spine threads), produce the **generic** full-rank
realization of the interior `v`-split `G_v^{ab} = G.splitOff v a b e₀` at an interior chain vertex
`v = cd.vtx i.castSucc` (`0 < i`), its successor neighbour `a = cd.vtx i.succ`, and its predecessor
neighbour `b = cd.vtx (i−1).castSucc`, with the fresh short-circuit label `e₀ = cd.e₀`.

This is the chain-arm analogue of the `removeVertex v` IH route the `d = 3` per-`i` setup runs
(`chainData_split_realization`'s `:670`-style `(hIH _ Gv hGvmin hGvne hGvlt).1 hGvSimple`), at the
*split-off* graph instead. The split-off is a smaller minimal `0`-dof-graph by KT 4.8(i)
(`splitOff_isMinimalKDof`, which under no-proper-rigid replaces KT's iterated swap with the green
`def = corank` count); it is simple by KT 6.7(ii) (`splitOff_simple_of_noRigid_of_card`: an
`ab`-parallel pair would close the triangle `G[{v,a,b}]`, a proper rigid subgraph at `4 ≤ |V(G)|`);
and it is strictly smaller (`splitOff_vertexSet_ncard_lt`, one vertex `v` removed). So the IH's
**GP `.1` conjunct** yields the generic realization — the seed `q` whose `IsGeneralPosition`
conjunct is the placement transversal and whose `AlgebraicIndependent` conjunct feeds the triple-LI
bridge (the data the bare `.2` conjunct cannot supply). It is the ONE genuinely-new datum the
general-`d` interior dispatch needs that no prior leaf supplies: it feeds both
the bottom basis-pick's `hfr` (the free `bottom_selection_of_crossFramework_span`, via the interior
`isInfinitesimallyRigidOn`/`finrank`-span identity) and the discriminator's `hsplitGP` input.
Consumes only the already-sanctioned C.3 `hIH` add; no cert/motive/wrapper change. -/
theorem PanelHingeFramework.interior_hsplitGP [DecidableEq β] [Finite α] [Finite β]
    {G : Graph α β} {n : ℕ} (cd : G.ChainData n) (i : Fin cd.d) (hi : 0 < (i : ℕ))
    (hD3 : 3 ≤ Graph.bodyBarDim n) (hV4 : 4 ≤ V(G).ncard) (hSimple : G.Simple)
    (hG : G.IsMinimalKDof n 0)
    (hnoRigid : ∀ H : Graph α β, ¬ H.IsProperRigidSubgraph G n)
    (hIH : ∀ (k' : ℤ) (G' : Graph α β), G'.IsMinimalKDof n k' → V(G').Nonempty →
      V(G').ncard < V(G).ncard →
      (G'.Simple → PanelHingeFramework.HasGenericFullRankRealization k n G') ∧
        HasPanelRealization k n G') :
    PanelHingeFramework.HasGenericFullRankRealization k n
      (G.splitOff (cd.vtx i.castSucc) (cd.vtx i.succ)
        (cd.vtx (⟨(i : ℕ) - 1, by omega⟩ : Fin cd.d).castSucc) cd.e₀) := by
  haveI := hSimple
  -- The interior-split tuple `(v, a, b, e_a, e_b)` read off the `ChainData` accessors.
  set v := cd.vtx i.castSucc with hv
  set a := cd.vtx i.succ with ha
  set b := cd.vtx (⟨(i : ℕ) - 1, by omega⟩ : Fin cd.d).castSucc with hb
  set e_a := cd.edge i with hea
  set e_b := cd.edge ⟨(i : ℕ) - 1, by omega⟩ with heb
  -- The two chain edges out of the split body `v`, the degree-2 closure, and the distinctnesses.
  have hlea : G.IsLink e_a v a := cd.isLink_succ_edge i
  have hleb : G.IsLink e_b v b := cd.isLink_pred_edge hi
  have hclv : ∀ e x, G.IsLink e v x → e = e_a ∨ e = e_b := cd.deg_two_split hi
  have heab : e_a ≠ e_b := (cd.pred_edge_ne hi).symm
  have hav : a ≠ v := (cd.castSucc_ne_succ i).symm
  have hbv : b ≠ v := (cd.castSucc_ne_pred_castSucc hi).symm
  have hvG : v ∈ V(G) := cd.vtx_mem _
  have haG : a ∈ V(G) := cd.vtx_mem _
  have hbG : b ∈ V(G) := cd.vtx_mem _
  have he₀ : cd.e₀ ∉ E(G) := cd.e₀_fresh
  have hV3 : 3 ≤ V(G).ncard := le_trans (by norm_num) hV4
  -- The `v`-split is a smaller minimal `0`-dof-graph (KT 4.8(i)), simple (KT 6.7(ii)), and strictly
  -- smaller; the IH's GP `.1` conjunct realizes it generically.
  have hGab : (G.splitOff v a b cd.e₀).IsMinimalKDof n 0 :=
    Graph.splitOff_isMinimalKDof (le_trans (by norm_num) hD3) hV3 hav hbv haG hbG hvG heab
      hlea hleb hclv he₀ hG hnoRigid
  have hGabSimple : (G.splitOff v a b cd.e₀).Simple :=
    Graph.splitOff_simple_of_noRigid_of_card hD3 heab hlea hleb hV4 hnoRigid
  have hGabne : V(G.splitOff v a b cd.e₀).Nonempty := by
    rw [Graph.vertexSet_splitOff]; exact ⟨a, haG, by simpa using hav⟩
  have hGablt : V(G.splitOff v a b cd.e₀).ncard < V(G).ncard :=
    Graph.splitOff_vertexSet_ncard_lt hvG
  exact (hIH _ (G.splitOff v a b cd.e₀) hGab hGabne hGablt).1 hGabSimple

/-- **CHAIN-2c-iii D-CAN-4 — the IH-bottom full-rank count `hfr₂`** (`lem:case-III` general-`d`;
Katoh–Tanigawa 2011 §6.4.2, Lemma 6.13; Phase 23f, `notes/Phase23-design.md` §(4.72.2)/(4.72.3)).
The bridge the interior dispatch (`chainData_dispatch`) consumes to feed the literal-IH-bottom
selector `bottom_selection_of_crossFramework_span_Gab`'s `hfr₂` slot: from the **def-0** IH-generic
full-rank realization `hsplitGP` of the split-off graph `G'` (the interior `G_v^{ab}`, supplied by
D1 `interior_hsplitGP`), unpack the realizing framework `Q` and re-express it as
`ofNormals G' Q.ends q` at the flattened seed `q = Q.normal`, then read off the IH's own rank
conjunct as the **`ℕ`-valued** rigidity-row-span finrank `= screwDim k · (|V(G')| − 1)` — the
cross-framework bottom block's full-rank count `R(Gab)` (KT eq.~(6.64), the `D·(|V|−2)` bottom of
the `_zero₁₂` cert).

The package bundles, against the single self-consistent `ofNormals G' Q.ends q` framework, the four
inputs the bottom selector + the cross-framework `hsupp`/`hgp` leaves consume: the seed's algebraic
independence `AlgebraicIndependent ℚ q` (for the discriminator pick), the general position
`IsGeneralPosition` (for `hgp₂`/`hne_Gv`), the edge link-recording `hends₂` (`Q.ends` records every
`G'`-link), and the `ℕ` finrank equation `hfr₂`. The placement `q := Q.normal` is the established
conflict-free pattern (`chainData_split_realization:907`, the d=3 `hQeq:303`); the `ℤ`→`ℕ` cast of
the IH rank conjunct goes through `def = 0` (`hdef`) + nonempty `|V(G')| ≥ 1` (`hne`). No `d = 3`
content, no cert/motive/IH change — pure IH-unpacking + a finrank cast. No `\lean` pin (internal
infra; the chain dispatch carries the blueprint node). -/
theorem PanelHingeFramework.exists_ofNormals_finrank_span_rigidityRows_eq_of_hsplitGP
    [Finite α] {n : ℕ} {G' : Graph α β}
    (hne : V(G').Nonempty) (hdef : G'.deficiency n = 0)
    (hsplitGP : PanelHingeFramework.HasGenericFullRankRealization k n G') :
    ∃ (q : α × Fin (k + 2) → ℝ) (ends : β → α × α),
      AlgebraicIndependent ℚ q ∧
      (PanelHingeFramework.ofNormals G' ends q).IsGeneralPosition ∧
      (∀ e u w, G'.IsLink e u w →
        G'.IsLink e ((PanelHingeFramework.ofNormals G' ends q).ends e).1
          ((PanelHingeFramework.ofNormals G' ends q).ends e).2) ∧
      Module.finrank ℝ (Submodule.span ℝ
          (PanelHingeFramework.ofNormals G' ends q).toBodyHinge.rigidityRows)
        = screwDim k * (V(G').ncard - 1) := by
  -- Unpack the IH realization and re-express it at the flattened seed `q := Q.normal`.
  obtain ⟨Q, hQg, hQgp, hQrank, hQrec, hQalg⟩ := hsplitGP
  set q : α × Fin (k + 2) → ℝ := fun p => Q.normal p.1 p.2 with hq
  have hQeq : PanelHingeFramework.ofNormals G' Q.ends q = Q := by rw [hq, ← hQg]; rfl
  refine ⟨q, Q.ends, hQalg, by rw [hQeq]; exact hQgp, ?_, ?_⟩
  · -- `Q.ends` records every `G'`-link (the `HasGenericFullRankRealization` link conjunct).
    intro e u w he
    rw [hQeq]
    rcases hQrec e u w he with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]; exact he
    · rw [h1, h2]; exact he.symm
  · -- The `ℕ` finrank equation from the IH's `ℤ` rank conjunct, via `def = 0` + nonempty.
    rw [hdef, sub_zero] at hQrank
    have h1 : 1 ≤ V(G').ncard := (Set.ncard_pos (Set.toFinite _)).2 hne
    rw [hQeq]
    have : ((Module.finrank ℝ (Submodule.span ℝ Q.toBodyHinge.rigidityRows) : ℤ))
        = ((screwDim k * (V(G').ncard - 1) : ℕ) : ℤ) := by
      rw [hQrank, Nat.cast_mul, Nat.cast_sub h1, Nat.cast_one]
    exact_mod_cast this

/-! ## The per-`i` gate-producer (CHAIN-2a-i, the W6b half)

The general-`d` Case-III chain dispatch (CHAIN-5) realizes each chain candidate `i` via the
already-general arm closer `case_III_arm_realization`, which carries the per-`i` gate family as
hypotheses (`hLn`/`hρgate`/`hρe₀`/`hρGv`/`hwcard`/`hw`/`hwmem`). The dispatch supplies that family
**from above** via two general-`k` producers: the W6b packaging
`exists_candidateRow_bottomRows_of_rigidOn` (the redundant-row + bottom-rows half:
`hρe₀`/`hρGv`/`hwcard`/`hw`/`hwmem`) and the Claim-6.12 discriminator
`exists_complementIso_ne_zero_of_homogeneousIncidence_gen` (the transversal half:
`hLn`/`hρgate`). This section packages the **first** of those two calls as a reusable single-split
producer, lifting the `d = 3` dispatch's W6b region (`case_III_candidate_dispatch` steps 3–4) to a
`{k}`-general flat-tuple lemma. The discriminator half — which picks the discriminating panel and so
needs the `Fin (k+1)` chain-panel-normal family — is the family-level glue (CHAIN-2c); the
`ChainData`-bound assembly that feeds the accessor-derived split tuple is CHAIN-2a-ii. -/

/-- **CHAIN-2a-i — the per-split W6b gate bundle** (`lem:case-III-claim-6-11` infra; Katoh–Tanigawa
2011 §6.4.1 eqs. (6.23), (6.27)–(6.30), Phase 23b). From an interior chain split `(v, a, b)` of a
simple `0`-dof-graph `G` — the degree-2 split body `v` with its two chain edges `e_a : v—a`,
`e_b : v—b` and no others, a fresh short-circuit `e₀`, and the IH-generic base realization
`hsplitGP` on `Gab = G.splitOff v a b e₀` — produce the candidate functional `ρ` and the
`screwDim k · (|V(Gab)| − 1)` independent bottom rows `w` that `case_III_arm_realization` consumes:
the redundant-row gate `hρe₀` (`ρ(C(ab)) = 0`), the span gate `hρGv`
(`hingeRow a b ρ ∈ span R(Gᵥ, q)`), and the bottom family `w` (independent, each a `Gᵥ`-row or a
candidate `ρ'`-hinge). The outputs are stated in **chain order `(a, b)`** — the `(a,b)`-vs-`(b,a)`
sign normalization of the dispatch's W8 pattern (`panelSupportExtensor_swap` / `hingeRow_swap`) is
absorbed here.

This is the **W6b half** of the per-`i` gate-producer: one call to
`exists_candidateRow_bottomRows_of_rigidOn` (already general-`k`), fed the eq.-(6.22) nested-IH
rank bound `h622lb` (supplied by the caller from `case_III_nested_rank_lower_all_k`) and the
unpacked IH base. The transversal gates `hLn`/`hρgate` come from the Claim-6.12 discriminator and
are *not* produced here — the discriminator's panel pick is the `Fin d` family glue (CHAIN-2c). No
`d = 3` content (graph-free over `ScrewSpace k`; the `Fin 4`/`⋀²ℝ⁴` discriminator is absent); no
motive/IH change. The `d = 3` dispatch `case_III_candidate_dispatch` consumes this at `k = 2`. -/
theorem PanelHingeFramework.chainData_split_w6b_gates
    [Finite α] [Finite β]
    (hk1 : 1 ≤ k) (G : Graph α β) (v a b : α) (e₀ : β)
    (hav : a ≠ v) (hbv : b ≠ v) (hba : b ≠ a)
    (haG : a ∈ V(G)) (hbG : b ∈ V(G))
    (he₀ : e₀ ∉ E(G))
    -- The eq.-(6.22) nested-IH rank bound at `Gᵥ = G − v`, in the `∀ ends q` carry shape (GAP 6);
    -- the caller supplies it from `case_III_nested_rank_lower_all_k`.
    (h622lb : ∀ (ends : β → α × α) (q : α × Fin (k + 2) → ℝ),
      (∀ e u w, (G.splitOff v a b e₀).IsLink e u w → ends e = (u, w) ∨ ends e = (w, u)) →
      (∀ x y : α, x ≠ y → LinearIndependent ℝ ![fun i => q (x, i), fun i => q (y, i)]) →
      AlgebraicIndependent ℚ q →
      screwDim k * (V(G.splitOff v a b e₀).ncard - 1) - (screwDim k - 2)
        ≤ Module.finrank ℝ (Submodule.span ℝ
            (PanelHingeFramework.ofNormals (G.removeVertex v) ends
              q).toBodyHinge.rigidityRows))
    {n : ℕ} (hdef_Gab : (G.splitOff v a b e₀).deficiency n = 0)
    (hsplitGP : PanelHingeFramework.HasGenericFullRankRealization k n (G.splitOff v a b e₀)) :
    ∃ (q : α × Fin (k + 2) → ℝ) (ends : β → α × α)
      (ρ : Module.Dual ℝ (ScrewSpace k))
      (w : Fin (screwDim k * (V(G.splitOff v a b e₀).ncard - 1)) →
        Module.Dual ℝ (α → ScrewSpace k))
      (lamAB : Fin (screwDim k - 1) → ℝ)
      (rab : Fin (screwDim k - 1) → Module.Dual ℝ (ScrewSpace k)),
      -- the base framework `(Gab, ends, q)` and its IH-genericity, for the consumer's other gates
      (PanelHingeFramework.ofNormals (G.splitOff v a b e₀) ends q).IsGeneralPosition ∧
      (∀ e u w, (G.removeVertex v).IsLink e u w →
        (G.removeVertex v).IsLink e (ends e).1 (ends e).2) ∧
      -- the chain-order-normalized W6b gate bundle (`na = q(a,·)`, `nb = q(b,·)`)
      ρ ≠ 0 ∧
      ρ (panelSupportExtensor (fun i => q (a, i)) (fun i => q (b, i))) = 0 ∧
      BodyHingeFramework.hingeRow a b ρ ∈ Submodule.span ℝ
        (PanelHingeFramework.ofNormals (G.removeVertex v) ends q).toBodyHinge.rigidityRows ∧
      LinearIndependent ℝ w ∧
      (∀ j, w j ∈
          (PanelHingeFramework.ofNormals (G.removeVertex v) ends q).toBodyHinge.rigidityRows ∨
        ∃ ρ' : Module.Dual ℝ (ScrewSpace k),
          ρ' (panelSupportExtensor (fun i => q (a, i)) (fun i => q (b, i))) = 0 ∧
          w j = BodyHingeFramework.hingeRow a b ρ') ∧
      -- the chain-order-normalized eq.-(6.52) `λ`-grouped `(ab)`-edge witness (A-1, Phase 23b):
      -- each `rab j` in the `e₀`-hinge-row block, `ρ = Σ_j λ_{(ab)j} (rab j)` (the per-edge witness
      -- the CHAIN-2c-ii-arm `hρGv` perp carrier `candidate_perp_two_incident_panels` consumes).
      (∀ j, rab j ∈ BodyHingeFramework.hingeRowBlock
        (PanelHingeFramework.ofNormals (G.splitOff v a b e₀) ends q).toBodyHinge e₀) ∧
      ρ = ∑ j, lamAB j • rab j ∧
      -- the **edge-grouped** `G_v`-row form of the candidate (CHAIN-2c-iii LEAF-4 widening, A-1-i;
      -- KT eq. (6.66)): the candidate row `hingeRow a b ρ ∈ span R(G_v)-rows` exposed as an
      -- explicit per-edge `hingeRow` combination over `G_v = G − v`'s links, each summand carrying
      -- its link `eⱼ = uⱼvⱼ` and block row `rv j ∈ r(p(eⱼ))`. This is the all-edge eq.-(6.52)/
      -- (6.66) data the CHAIN-2c-ii-arm regroup-at-interior-degree-2-vertex carrier
      -- `candidate_perp_two_incident_panels` consumes (collect the summands incident to the
      -- interior chain vertex; the rest form the column-vanishing remainder). Already computed
      -- inside the W6b producer; re-exposed here (previously discarded) for the LEAF-4
      -- interior-`hρe₀` leaf.
      (∃ (nGv : ℕ) (cGv : Fin nGv → ℝ) (evGv : Fin nGv → β) (uvGv vvGv : Fin nGv → α)
          (rvGv : Fin nGv → Module.Dual ℝ (ScrewSpace k)),
        (∀ j, (G.removeVertex v).IsLink (evGv j) (uvGv j) (vvGv j)) ∧
        (∀ j, rvGv j ∈ ((PanelHingeFramework.ofNormals (G.removeVertex v) ends q).toBodyHinge
          ).hingeRowBlock (evGv j)) ∧
        BodyHingeFramework.hingeRow a b ρ
          = ∑ j, cGv j • BodyHingeFramework.hingeRow (uvGv j) (vvGv j) (rvGv j)) ∧
      -- the seed's algebraic independence (the discriminator-pick prerequisite, CHAIN-2c-iii
      -- LEAF-3): the IH-generic `v`-split realization's `AlgebraicIndependent ℚ` conjunct,
      -- re-exposed so `exists_chainData_discriminator_pick` can fire off this same `q`.
      AlgebraicIndependent ℚ q ∧
      -- the **full `Gab`-link recording disjunction** (incl. the fresh `e₀`): `ends` records every
      -- `Gab = G.splitOff v a b e₀` link as `(u,w)` or `(w,u)` (KT §6.4.2; §(4.100) (B′)). Already
      -- computed internally (`hrec'`); re-exposed (previously the weaker `Gv`-only `hends'` was
      -- returned) so the §(4.100) interior-arm `hρGv` leaf re-target + the bottom-relabel
      -- `chainData_bottom_relabel` can read the genuine base recording at `ends₀`.
      (∀ e u w, (G.splitOff v a b e₀).IsLink e u w → ends e = (u, w) ∨ ends e = (w, u)) := by
  classical
  haveI : Fintype α := Fintype.ofFinite α
  set Gab := G.splitOff v a b e₀ with hGab
  set Gv := G.removeVertex v with hGv
  -- 1. Unpack the generic `v`-split realization; re-express `Q` as `ofNormals Gab Q.ends q`.
  obtain ⟨Q, hQg, hQgp, hQrank, hQrec, hQalg⟩ := hsplitGP
  set q : α × Fin (k + 2) → ℝ := fun p => Q.normal p.1 p.2 with hq
  have hQeq : PanelHingeFramework.ofNormals Gab Q.ends q = Q := by rw [hq, ← hQg]; rfl
  have hgp' : (PanelHingeFramework.ofNormals Gab Q.ends q).IsGeneralPosition := by
    rw [hQeq]; exact hQgp
  have hne' : V(Gab).Nonempty := ⟨a, by rw [hGab, Graph.vertexSet_splitOff]; exact ⟨haG, by
    simp [hav]⟩⟩
  have hne_Q : Q.toBodyHinge.graph.vertexSet.Nonempty := by
    rw [PanelHingeFramework.toBodyHinge_graph, hQg]; exact hne'
  rw [hdef_Gab, sub_zero] at hQrank
  have hVeq_Gab : V(Gab) = Q.toBodyHinge.graph.vertexSet := by
    rw [PanelHingeFramework.toBodyHinge_graph, hQg]
  have h1_Gab : 1 ≤ V(Gab).ncard := (Set.ncard_pos (Set.toFinite _)).2 hne'
  have hQrig : Q.toBodyHinge.IsInfinitesimallyRigidOn V(Gab) := by
    rw [hVeq_Gab,
      BodyHingeFramework.isInfinitesimallyRigidOn_vertexSet_iff_finrank_span_rigidityRows
        Q.toBodyHinge hne_Q, ← hVeq_Gab]
    zify [h1_Gab] at hQrank ⊢; exact_mod_cast hQrank
  have hrig' : (PanelHingeFramework.ofNormals Gab Q.ends q).toBodyHinge.IsInfinitesimallyRigidOn
      V(Gab) := by rw [hQeq]; exact hQrig
  have hrec' : ∀ e u w, Gab.IsLink e u w → Q.ends e = (u, w) ∨ Q.ends e = (w, u) := by
    intro e u w he
    rcases hQrec e u w he with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl (Prod.ext h1 h2)
    · exact Or.inr (Prod.ext h1 h2)
  -- 2. Inline graph facts.
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
  have hgp_seed : ∀ x y : α, x ≠ y →
      LinearIndependent ℝ ![fun i => q (x, i), fun i => q (y, i)] := by
    intro x y hxy
    have := hgp' x y hxy
    rw [PanelHingeFramework.ofNormals_normal, PanelHingeFramework.ofNormals_normal] at this
    exact this
  -- `hends'`: `Q.ends` records the links of `Gv` (`Gv`-links are `Gab`-links via `hle`).
  have hends' : ∀ e u w, Gv.IsLink e u w → Gv.IsLink e (Q.ends e).1 (Q.ends e).2 := by
    intro e u w hlink
    rcases hrec' e u w (hle e u w hlink) with he | he
    · rw [he]; exact hlink
    · rw [he]; exact hlink.symm
  -- 3. W6b: one invocation extracting the candidate / bottom data (the redundancy + GAP-6 half).
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
      (h622lb Q.ends q hrec' hgp_seed hQalg)
  -- 4. Normalize the W6b outputs to chain order `(a, b)` (the W8 sign-swap pattern).
  set na := (fun i => q (a, i)) with hna
  set nb := (fun i => q (b, i)) with hnb
  -- The `supportExtensor e₀`-form annihilation in `panelSupportExtensor` form.
  have hsupp_e₀ : ∀ (r : Module.Dual ℝ (ScrewSpace k)),
      r ((PanelHingeFramework.ofNormals Gab Q.ends q).toBodyHinge.supportExtensor e₀) =
        r (panelSupportExtensor (fun i => q ((Q.ends e₀).1, i))
          (fun i => q ((Q.ends e₀).2, i))) := by
    intro r
    rw [PanelHingeFramework.toBodyHinge_supportExtensor, PanelHingeFramework.ofNormals_ends,
      PanelHingeFramework.ofNormals_normal, PanelHingeFramework.ofNormals_normal]
  refine ⟨q, Q.ends, ?_⟩
  rcases hrec' e₀ a b he₀ab with he | he
  · -- recorded `(a, b)`: take `ρ` as is.
    refine ⟨ρ, w, lamAB, rab, hgp', hends', hρne, ?_, ?_, hw, ?_, hrab_blk, hρ_lam, ?_, hQalg,
      hrec'⟩
    · rw [hsupp_e₀, he] at hρe₀'; exact hρe₀'
    · rw [he] at hρGv'; exact hρGv'
    · intro j
      rcases hwmem' j with hgen | ⟨ρ', hρ'e₀, hwj⟩
      · exact Or.inl hgen
      · refine Or.inr ⟨ρ', ?_, by rw [hwj, he]⟩
        rw [hsupp_e₀, he] at hρ'e₀; exact hρ'e₀
    · -- the edge-grouped `G_v`-row form (eq. (6.66)): `Q.ends e₀ = (a, b)`, so the candidate row
      -- `hingeRow a b ρ` is the producer's `hingeRow (Q.ends e₀).1 (Q.ends e₀).2 ρ` verbatim.
      obtain ⟨nGv, cGv, evGv, uvGv, vvGv, rvGv, hlinkGv, hrvGv, hcombGv⟩ := hedgeGv
      exact ⟨nGv, cGv, evGv, uvGv, vvGv, rvGv, hlinkGv, hrvGv, by rw [he] at hcombGv; exact hcombGv⟩
  · -- recorded `(b, a)`: take `-ρ` (`hingeRow b a (-ρ) = hingeRow a b ρ`); negate the witness
    -- `rab → -rab` (the block is a subspace, `-ρ = Σ_j λ_j (-rab j)`).
    refine ⟨-ρ, w, lamAB, fun j => -rab j, hgp', hends', neg_ne_zero.mpr hρne, ?_, ?_, hw, ?_,
      fun j => (PanelHingeFramework.ofNormals Gab Q.ends q).toBodyHinge.hingeRowBlock e₀ |>.neg_mem
        (hrab_blk j), ?_, ?_, hQalg, hrec'⟩
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
    · -- the edge-grouped `G_v`-row form (eq. (6.66)): `Q.ends e₀ = (b, a)`, output `ρ` is `-ρ`. The
      -- candidate row `hingeRow a b (-ρ) = hingeRow b a ρ` (`hingeRow_swap`) is the producer's
      -- `hingeRow (Q.ends e₀).1 (Q.ends e₀).2 ρ`; the edge-grouped RHS is unchanged.
      obtain ⟨nGv, cGv, evGv, uvGv, vvGv, rvGv, hlinkGv, hrvGv, hcombGv⟩ := hedgeGv
      refine ⟨nGv, cGv, evGv, uvGv, vvGv, rvGv, hlinkGv, hrvGv, ?_⟩
      rw [he] at hcombGv
      rw [BodyHingeFramework.hingeRow_swap a b (-ρ), neg_neg]; exact hcombGv

/-- **The chain length equals `k + 1`** (`lem:case-III` general-`d`, the discriminator-index
identity; Katoh–Tanigawa 2011 §6.4.2): from the `ChainData` field `d_eq : d = n` and the ambient
body-bar dimension constraint `hn : bodyBarDim n = screwDim k`, the chain length `cd.d` equals
`k + 1`. This is the dispatch-side companion of `d_eq` that closes the **discriminator-index gap**
(Phase 23c §I.8.24(4.11)): the Claim-6.12 panel discriminator
(`exists_chainData_discriminator_pick`, `exists_complementIso_ne_zero_of_homogeneousIncidence_gen`)
is `Fin (k+1)`-indexed (one panel per chain candidate), while the chain candidate index ranges over
`Fin cd.d`; the two index sets align only via `cd.d = k + 1`. KT §6.4.2 forces this structurally —
the `d` candidate frameworks are the `d` panels (eq. 6.67), and the dimension count
`D = (d+1 choose 2) = screwDim k = (k+2 choose 2)` gives `d + 1 = k + 2` (eq. 6.46/6.67).

The arithmetic: `cd.d = n` (the `d_eq` field), and `n = k + 1` from `hn` — the body-bar dimension
`bodyBarDim n = n(n+1)/2` and screw dimension `screwDim k = (k+2 choose 2) = (k+2)(k+1)/2` clear to
the product equation `n(n+1) = (k+2)(k+1)` (each numerator even, `Nat.mul_div_cancel'`), whose only
solution in `ℕ` is `n = k + 1` (`nlinarith`). No `d = 3` content; at the `d = 3` regime `n = 3`,
`k = 2`, so `cd.d = 3 = 2 + 1` is the zero-regression specialization. -/
theorem _root_.Graph.ChainData.d_eq_kAdd {G : Graph α β} {n : ℕ} (cd : G.ChainData n)
    (hn : Graph.bodyBarDim n = screwDim k) : cd.d = k + 1 := by
  have key : ∀ m : ℕ, 2 * Nat.choose m 2 = m * (m - 1) := fun m => by
    rw [Nat.choose_two_right, Nat.mul_div_cancel' (Nat.even_mul_pred_self m).two_dvd]
  have hbb : 2 * Graph.bodyBarDim n = n * (n + 1) := by
    rw [Graph.bodyBarDim, Nat.mul_div_cancel' (Nat.even_mul_succ_self n).two_dvd]
  have hsd : 2 * screwDim k = (k + 2) * (k + 1) := by
    rw [show screwDim k = Nat.choose (k + 2) 2 from rfl, key (k + 2),
      show k + 2 - 1 = k + 1 from rfl]
  have hprod : n * (n + 1) = (k + 2) * (k + 1) := by omega
  have hnk : n = k + 1 := by nlinarith [hprod]
  rw [cd.d_eq, hnk]

/-- **The Case-III panel selector, transported to `Fin (k + 1)`** (`lem:case-III` general-`d`,
CHAIN-2c-iii LEAF-3; Katoh–Tanigawa 2011 §6.4.2 eq. 6.67). The composition of the record-local
panel→vertex selector `candidateVtx : Fin cd.d → α` (eq. 6.67, `Π₀ = Π(v₀)`, `Πᵢ = Π(v_{i+1})`) with
the index transport `Fin.cast (cd.d_eq_kAdd hn).symm : Fin (k + 1) → Fin cd.d` across the
chain-length identity `cd.d = k + 1` (`d_eq_kAdd`). This is the `cand : Fin (k + 1) → α` selector
the Claim-6.12 panel discriminator `exists_chainData_discriminator_pick` consumes: it tests one
panel `Π(cand u)` per discriminator index `u : Fin (k + 1)`, and `cand` must be injective (the
panels distinct). The
discriminator-index gap (Phase 23c §I.8.24(4.11)) is exactly this `Fin (k + 1)`-vs-`Fin cd.d`
reconciliation; `d_eq_kAdd` closes it structurally (KT's `d` candidates = `d` panels = same index
set). No `d = 3` content; at `d = 3` (`n = 3`, `k = 2`) it is `Fin 3 → α` unchanged. -/
def _root_.Graph.ChainData.candidatePanel {G : Graph α β} {n : ℕ} (cd : G.ChainData n)
    (hn : Graph.bodyBarDim n = screwDim k) : Fin (k + 1) → α :=
  cd.candidateVtx ∘ Fin.cast (cd.d_eq_kAdd hn).symm

/-- The panel selector unfolds to `candidateVtx` at the transported index (CHAIN-2c-iii LEAF-3): the
named bridge routing the discriminator's panel `u : Fin (k + 1)` to the chain candidate
`Fin.cast (cd.d_eq_kAdd hn).symm u : Fin cd.d`. Composing with `candidateVtx_succ_eq`
(`candidateVtx i = vtx i.succ` at interior `i`) turns the discriminator's gate at `cand u` into the
chain arm's gate at the successor neighbour `vtx (Fin.cast … u).succ`. -/
lemma _root_.Graph.ChainData.candidatePanel_apply {G : Graph α β} {n : ℕ} (cd : G.ChainData n)
    (hn : Graph.bodyBarDim n = screwDim k) (u : Fin (k + 1)) :
    cd.candidatePanel hn u = cd.candidateVtx (Fin.cast (cd.d_eq_kAdd hn).symm u) := rfl

/-- **The transported panel selector is injective** (CHAIN-2c-iii LEAF-3): the
`Function.Injective cand` half of the discriminator's `cand : Fin (k + 1) → α` input, composing
`candidateVtx_injective` (the chain vertices `v₀, v₂, …, v_d` distinct) with the bijection
`Fin.cast (cd.d_eq_kAdd hn).symm`. -/
lemma _root_.Graph.ChainData.candidatePanel_injective {G : Graph α β} {n : ℕ} (cd : G.ChainData n)
    (hn : Graph.bodyBarDim n = screwDim k) : Function.Injective (cd.candidatePanel hn) :=
  cd.candidateVtx_injective.comp (Fin.cast_injective _)

/-- **CHAIN-2a-ii — the per-`i` chain-candidate reduction core** (`lem:case-III`; Katoh–Tanigawa
2011 §6.4.1, Lemma 6.13 the per-candidate arm; Phase 23b). For an interior chain index `i`
(`0 < i`, so `vᵢ` is a degree-2 chain vertex with chain edges `edge i : vᵢ—vᵢ₊₁` and the
predecessor `edge (i−1) : vᵢ—vᵢ₋₁`), this re-indexes the already-general arm closer
`case_III_arm_realization` off the `ChainData` interior-split accessors: the split body is
`v := vtx i.castSucc`, its successor neighbour `a := vtx i.succ` (via `e_a := edge i`), its
predecessor neighbour `b := vtx (i−1).castSucc` (via `e_b := edge (i−1)`), and the interior
degree-2 closure (`deg_two_split`) says those are the only two `G`-edges at `v`.

The per-`i` gate family the arm closer carries is threaded **from above** by two general-`k`
producers, exactly as the `d = 3` dispatch (`case_III_candidate_dispatch`): the W6b bundle
`hρe₀`/`hρGv`/`hw`/`hwmem` from `chainData_split_w6b_gates` (fed the eq.-(6.22) nested-IH rank bound
from `case_III_nested_rank_lower_all_k`), and the **transversal** gate `hLn`/`hρgate` carried as the
hypothesis `htrans` — the contribution of the Claim-6.12 discriminator
(`exists_complementIso_ne_zero_of_homogeneousIncidence_gen`) once it has picked the panel `u`
matching this candidate `i`. That panel↔candidate match is the `Fin d` family glue **CHAIN-2c**
discharges (the discriminator picks an *arbitrary* `u`); here `htrans` is the single-`i` slot it
fills. So this is a pure re-index — no new linear algebra, no `d = 3` content (the `Fin 4`/`⋀²ℝ⁴`
discriminator is absent), no motive/IH change. The `ends₁`-override congruence (the W6b outputs are
stated at the split realization's selector; the arm closer reads them at the re-inserted-hinge
override `ends₁`) is the `rigidityRows_ofNormals_congr_ends` step, verbatim from the dispatch. -/
theorem PanelHingeFramework.chainData_split_realization
    [DecidableEq β] [Finite α] [Finite β]
    {G : Graph α β} {n : ℕ} (cd : G.ChainData n) (i : Fin cd.d) (hi : 0 < (i : ℕ))
    (hk1 : 1 ≤ k) (hn : Graph.bodyBarDim n = screwDim k)
    (hG : G.IsMinimalKDof n 0) (hV3 : 3 ≤ V(G).ncard) (hSimple : G.Simple)
    (hIH : ∀ (k' : ℤ) (G' : Graph α β), G'.IsMinimalKDof n k' → V(G').Nonempty →
      V(G').ncard < V(G).ncard →
      (G'.Simple → PanelHingeFramework.HasGenericFullRankRealization k n G') ∧
        HasPanelRealization k n G')
    (hdef_Gab :
      (G.splitOff (cd.vtx i.castSucc) (cd.vtx i.succ)
        (cd.vtx (⟨(i : ℕ) - 1, by omega⟩ : Fin cd.d).castSucc) cd.e₀).deficiency n = 0)
    (hdef : G.deficiency n = 0)
    (hsplitGP : PanelHingeFramework.HasGenericFullRankRealization k n
      (G.splitOff (cd.vtx i.castSucc) (cd.vtx i.succ)
        (cd.vtx (⟨(i : ℕ) - 1, by omega⟩ : Fin cd.d).castSucc) cd.e₀))
    -- The **transversal** half of the per-`i` gate family, the single-`i` slot the Claim-6.12
    -- discriminator fills (CHAIN-2c supplies it once it matches the discriminator's panel `u` to
    -- this candidate `i`): for the W6b candidate functional `ρ` (`ρ ≠ 0`, annihilating the chain
    -- support extensor `C(ab)`), a transversal normal `n'` of `Π(a)` with `ρ(C(a, n')) ≠ 0`.
    (htrans : ∀ (q : α × Fin (k + 2) → ℝ) (ends : β → α × α)
        (ρ : Module.Dual ℝ (ScrewSpace k)),
      (PanelHingeFramework.ofNormals (G.splitOff (cd.vtx i.castSucc) (cd.vtx i.succ)
        (cd.vtx (⟨(i : ℕ) - 1, by omega⟩ : Fin cd.d).castSucc) cd.e₀) ends q).IsGeneralPosition →
      ρ ≠ 0 →
      ρ (panelSupportExtensor (fun j => q (cd.vtx i.succ, j))
        (fun j => q (cd.vtx (⟨(i : ℕ) - 1, by omega⟩ : Fin cd.d).castSucc, j))) = 0 →
      ∃ n' : Fin (k + 2) → ℝ,
        LinearIndependent ℝ ![(fun j => q (cd.vtx i.succ, j)), n'] ∧
        ρ (panelSupportExtensor (fun j => q (cd.vtx i.succ, j)) n') ≠ 0) :
    PanelHingeFramework.HasGenericFullRankRealization k n G := by
  classical
  haveI : Fintype α := Fintype.ofFinite α
  -- The interior-split tuple `(v, a, b, e_a, e_b)` read off the `ChainData` accessors.
  set v := cd.vtx i.castSucc with hv
  set a := cd.vtx i.succ with ha
  set b := cd.vtx (⟨(i : ℕ) - 1, by omega⟩ : Fin cd.d).castSucc with hb
  set e_a := cd.edge i with hea
  set e_b := cd.edge ⟨(i : ℕ) - 1, by omega⟩ with heb
  -- The two chain edges, oriented *out of* the split body `v` (the accessors).
  have hlea : G.IsLink e_a v a := cd.isLink_succ_edge i
  have hleb : G.IsLink e_b v b := cd.isLink_pred_edge hi
  -- The interior degree-2 closure at `v`: every `G`-edge at `v` is `e_a` or `e_b`.
  have hclv : ∀ e x, G.IsLink e v x → e = e_a ∨ e = e_b := cd.deg_two_split hi
  -- Distinctness of the tuple, from `vtx_inj`/`edge_inj`.
  have hba : b ≠ a := (cd.succ_ne_pred_castSucc hi).symm
  have heab : e_a ≠ e_b := (cd.pred_edge_ne hi).symm
  have hav : a ≠ v := fun h => by
    have := congrArg Fin.val (cd.vtx_inj h)
    simp only [Fin.val_succ, Fin.val_castSucc] at this; omega
  have hbv : b ≠ v := fun h => by
    have := congrArg Fin.val (cd.vtx_inj h)
    simp only [Fin.val_castSucc] at this; omega
  have hvG : v ∈ V(G) := cd.vtx_mem _
  have haG : a ∈ V(G) := cd.vtx_mem _
  have hbG : b ∈ V(G) := cd.vtx_mem _
  have he₀ : cd.e₀ ∉ E(G) := cd.e₀_fresh
  haveI hGloop : G.Loopless := hSimple.toLoopless
  set Gv := G.removeVertex v with hGv
  haveI : Gv.Loopless := hGloop.mono (hGv ▸ Graph.removeVertex_le G v)
  -- The eq.-(6.22) nested-IH rank bound at `Gv`, for the W6b producer's `h622lb` slot.
  have h622lb := PanelHingeFramework.case_III_nested_rank_lower_all_k hk1 hn G v a b e_a e_b cd.e₀
    hG hV3 hSimple hba hav hbv heab hlea hleb hclv he₀ hIH
  -- W6b half: the candidate functional `ρ`, the bottom rows `w`, and the W6b gate bundle.
  obtain ⟨q, ends, ρ, w, _lamAB, _rab, hgp_split, hends', hρne, hρe₀, hρGv', hw, hwmem',
      _hrab_blk, _hρ_lam, _hedgeGv, _hQalg, _hrecGab⟩ :=
    PanelHingeFramework.chainData_split_w6b_gates hk1 G v a b cd.e₀ hav hbv hba haG hbG he₀
      h622lb hdef_Gab hsplitGP
  set na := (fun j => q (a, j)) with hna
  set nb := (fun j => q (b, j)) with hnb
  -- The transversal gate from `htrans`, at the W6b candidate `ρ`.
  obtain ⟨n', hLn, hρgate⟩ := htrans q ends ρ hgp_split hρne hρe₀
  -- `hgab = ![na, nb] LI`, from the split realization's general position.
  have hgab : LinearIndependent ℝ ![na, nb] := by
    have := hgp_split a b hba.symm
    rwa [PanelHingeFramework.ofNormals_normal, PanelHingeFramework.ofNormals_normal] at this
  -- Common `Gv`/`G` facts shared with the dispatch's M₁ arm.
  have hvVc : v ∉ V(Gv) := by rw [hGv, Graph.vertexSet_removeVertex]; exact fun h => h.2 rfl
  have haVc : a ∈ V(Gv) := by rw [hGv, Graph.vertexSet_removeVertex]; exact ⟨haG, hav⟩
  have hbVc : b ∈ V(Gv) := by rw [hGv, Graph.vertexSet_removeVertex]; exact ⟨hbG, hbv⟩
  have hleG : ∀ e u w, Gv.IsLink e u w → G.IsLink e u w := by
    intro e u w hlink; rw [hGv, Graph.removeVertex_isLink] at hlink; exact hlink.1
  have hGv_off : ∀ {e u w}, Gv.IsLink e u w → e ≠ e_a ∧ e ≠ e_b := by
    intro e u w hlink
    rw [hGv, Graph.removeVertex_isLink] at hlink
    obtain ⟨hGlink, hunev, hwnev⟩ := hlink
    refine ⟨fun he => ?_, fun he => ?_⟩
    · subst he
      rcases hlea.eq_and_eq_or_eq_and_eq hGlink with ⟨hh, _⟩ | ⟨hh, _⟩
      · exact hunev hh.symm
      · exact hwnev hh.symm
    · subst he
      rcases hleb.eq_and_eq_or_eq_and_eq hGlink with ⟨hh, _⟩ | ⟨hh, _⟩
      · exact hunev hh.symm
      · exact hwnev hh.symm
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
    rw [hGv, Graph.vertexSet_removeVertex, Set.ncard_diff_singleton_of_mem hvG]; omega
  have hVcard : V(G).ncard = V(Gv).ncard + 1 := by
    rw [hGv, Graph.vertexSet_removeVertex, Set.ncard_diff_singleton_of_mem hvG]; omega
  have hcard : V(G.splitOff v a b cd.e₀).ncard = V(Gv).ncard := by
    rw [hGv, Graph.vertexSet_splitOff, Graph.vertexSet_removeVertex]
  -- The M₁ arm selector `ends₁` overriding `ends` at the two re-inserted hinges `e_a`, `e_b`.
  set ends₁ : β → α × α := Function.update (Function.update ends e_a (v, a)) e_b (v, b)
    with hends₁
  have hends₁_off : ∀ {e}, e ≠ e_a → e ≠ e_b → ends₁ e = ends e := by
    intro e hea heb
    rw [hends₁, Function.update_of_ne heb, Function.update_of_ne hea]
  have hcongr : (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge.rigidityRows
      = (PanelHingeFramework.ofNormals Gv ends₁ q).toBodyHinge.rigidityRows :=
    PanelHingeFramework.rigidityRows_ofNormals_congr_ends q
      (fun e u w hlink => (hends₁_off (hGv_off hlink).1 (hGv_off hlink).2).symm)
  have hends_ea₁ : ends₁ e_a = (v, a) := by
    rw [hends₁, Function.update_of_ne heab, Function.update_self]
  have hends_eb₁ : ends₁ e_b = (v, b) := by rw [hends₁, Function.update_self]
  have hends_Gv₁ : ∀ e u w, Gv.IsLink e u w → Gv.IsLink e (ends₁ e).1 (ends₁ e).2 := by
    intro e u w hlink
    obtain ⟨hne_a, hne_b⟩ := hGv_off hlink
    rw [hends₁_off hne_a hne_b]
    exact hends' e u w hlink
  have hne_Gv₁ : ∀ e, Gv.IsLink e (ends₁ e).1 (ends₁ e).2 →
      (PanelHingeFramework.ofNormals Gv ends₁ q).toBodyHinge.supportExtensor e ≠ 0 := by
    intro e hlink
    apply PanelHingeFramework.supportExtensor_ne_zero_of_isGeneralPosition
    · intro x y hxy
      rw [PanelHingeFramework.ofNormals_normal, PanelHingeFramework.ofNormals_normal]
      have := hgp_split x y hxy
      rwa [PanelHingeFramework.ofNormals_normal, PanelHingeFramework.ofNormals_normal] at this
    · rw [PanelHingeFramework.ofNormals_ends]; exact hlink.ne
  -- The W6b span gate `hρGv` and bottom-rows `hwmem`, rewritten through `hcongr` into `ends₁`-rows.
  have hρGv : BodyHingeFramework.hingeRow a b ρ ∈ Submodule.span ℝ
      (PanelHingeFramework.ofNormals Gv ends₁ q).toBodyHinge.rigidityRows := by
    rw [← hcongr]; exact hρGv'
  have hwmem : ∀ j, w j ∈ (PanelHingeFramework.ofNormals Gv ends₁ q).toBodyHinge.rigidityRows ∨
      ∃ ρ' : Module.Dual ℝ (ScrewSpace k),
        ρ' (panelSupportExtensor na nb) = 0 ∧ w j = BodyHingeFramework.hingeRow a b ρ' := by
    intro j
    rcases hwmem' j with hgen | hcand
    · exact Or.inl (by rw [← hcongr]; exact hgen)
    · exact Or.inr hcand
  -- Re-index the arm closer at the `cd`-derived split tuple.
  refine PanelHingeFramework.case_III_arm_realization (k := k) G Gv ends₁ (q := q)
    (v := v) (a := a) (b := b) (e_a := e_a) (e_b := e_b) (n' := n')
    hvVc haVc hbVc hlea hleb hends_ea₁ hends_eb₁ heab hleG hsplitG hends_Gv₁ hne_Gv₁
    hVone hVcard hLn hgab hρgate hρe₀ hρGv (ιb := _) (w := w) ?_ hw hwmem hdef
  rw [Nat.card_fin, hcard]

/-- **CHAIN-2c-ii-arm — the honest interior-arm realization, sourcing `±r` via the eq.-(6.27) row-op
of a bottom `G−vᵢ`-row** (`lem:case-III` general-`d`; Katoh–Tanigawa 2011 §6.4.2, Lemma 6.13 the
interior per-`i` arm; eqs.~(6.56)/(6.59)/(6.64)/(6.66); Phase 23f, `notes/Phase23-design.md`
§(4.94)/(4.95)/(4.100)). The `ChainData`-indexed honest interior arm for a matched interior chain
candidate `i` (`2 ≤ i`), routing the degree-2 chain body `v := vtx i.castSucc` through the **honest
engine** `case_III_arm_realization` (the `hρGv`-collapse certification, already general-`k`) at the
candidate seed `qρ = q ∘ shiftPerm i.castSucc` — **abandoning** the diverged
`rigidityMatrixEdgeAug`/`hr ∈ span` interface (the §(4.93) wall). It is the all-`i` generalization
of the `d = 3` `M₃` arm `case_III_arm_realization_M3` (its `i = 2` single-swap instance), with the
single swap `Equiv.swap a v` replaced by the `(i−1)`-cycle relabel `shiftPerm i.castSucc` and the
crux `hρGv` slot fed by the landed `chainData_relabel_arm_hρGv` (§(4.95)/§(4.100)).

**The §(4.100) selector re-target.** The crux `hρGv` and bottom `hwmem` rows are stated at the
HONEST base selector `ends₀` (where the §(4.100)-re-targeted leaves
`chainData_relabel_arm_hρGv`/`chainData_bottom_relabel` produce them — NOT the global relabel-image
`candidateEnds`, which the fold's per-step gate cannot reach, §(4.100) (P-C)). The engine framework
runs at the SPARSE `Function.update` override `endsσρ₁` (the M₃ `ends₃` pattern, dispatch-supplied),
which forces the split-body-first orientation at the two re-inserted chain hinges `{e_a, e_b}` and
AGREES with `ends₀` off them (`hoff`). Since both override edges LINK the removed body `vᵢ`, they
are NOT `Gv = G − vᵢ`-links, so `ends₀` and `endsσρ₁` agree on every `Gv`-link; the
`ends₀`-stated `hρGv`/`hwmem` bridge to the `endsσρ₁`-engine rows via
`rigidityRows_ofNormals_congr_ends` (the M₃ `hcongr`, Probe E2). The candidate seed is the
inverse-cycle relabel `qρ = q ∘ shiftPerm i.castSucc` (KT eq.~(6.56)). The engine roles are the
interior split tuple `(v, a, b, e_a, e_b) := (vtx i.castSucc, vtx i.succ, vtx (i−1).castSucc,
edge i, edge (i−1))` and the candidate functional `ρ̃ := -ρ₀` (the M₃ sign convention:
`hingeRow a b (-ρ₀) = hingeRow b a ρ₀`).

Below the C.0–C.6 contract + the 0-dof motive: no new linear algebra in the arm itself — the gate
slots `hLn`/`hgab`/`hρgate`/`hρe₀` reduce through the landed seed reads
`seedShift_succ_castSucc`/`seedShift_pred_castSucc` (`qρ(a,·) = q(vtx i.succ,·)`,
`qρ(b,·) = q(vtx i.castSucc,·)`, the cycle analogues of `M₃`'s `hqρc`/`hqρv`), the `hρGv` slot is
the landed crux leaf (`§(4.95)/(4.100)`, collision-free in the honest engine — the eq.-(6.27)
row-op decouples the gate from the membership), and the structural/bottom slots are
dispatch-supplied (the override-`endsσρ₁`-recorded reinserted hinges + the surviving-`Gv` links +
the per-member relabelled bottom family `chainData_bottom_relabel`). No `\lean` pin (internal infra;
the chain dispatch carries the blueprint node). -/
theorem PanelHingeFramework.chainData_interior_realization_hρGv
    [DecidableEq α] [DecidableEq β] [Finite α] [Finite β]
    {G : Graph α β} {n : ℕ} (cd : G.ChainData n) (i : Fin cd.d) (h2i : 2 ≤ (i : ℕ))
    {ends₀ : β → α × α} {q : α × Fin (k + 2) → ℝ}
    {ρ₀ : Module.Dual ℝ (ScrewSpace k)} {n' : Fin (k + 2) → ℝ}
    -- THE ORIENTATION-OVERRIDE SELECTOR (the M₃ `ends₃` pattern, §(4.96) fix (A) / §(4.100) (E2)):
    -- the dispatch builds `endsσρ₁ := Function.update (Function.update ends₀ (edge i) (v, a))`
    -- `(edge (i−1)) (v, b)` to FORCE the split-body-first orientation at the two re-inserted chain
    -- hinges (the honest base selector `ends₀` records each link only up to the IH's free
    -- orientation, so it cannot force them). It AGREES with `ends₀` off the two chain edges
    -- (`hoff`), so the `hρGv`/`hwmem` rows — stated at the HONEST `ends₀` (where the §(4.100)-
    -- re-targeted leaves produce them) — bridge to `endsσρ₁` on the surviving `Gv`-links via
    -- `rigidityRows_ofNormals_congr_ends`. The two override edges `{edge i, edge (i−1)}` both LINK
    -- the removed body `vᵢ`, so they are NOT `Gv = G − vᵢ`-links and the sparse override passes
    -- through on every `Gv`-link (Probe E2).
    (endsσρ₁ : β → α × α)
    (hoff : ∀ e, e ≠ cd.edge i → e ≠ cd.edge ⟨(i : ℕ) - 1, by have := i.isLt; omega⟩ →
      endsσρ₁ e = ends₀ e)
    -- the OVERRIDE selector `endsσρ₁` records the two reinserted chain hinges at the split body
    -- `v = vtx i.castSucc`, split-body-first (dispatch-supplied; `rfl` once `endsσρ₁` is the
    -- update):
    (hends_ea : endsσρ₁ (cd.edge i) = (cd.vtx i.castSucc, cd.vtx i.succ))
    (hends_eb : endsσρ₁ (cd.edge ⟨(i : ℕ) - 1, by have := i.isLt; omega⟩)
      = (cd.vtx i.castSucc, cd.vtx (⟨(i : ℕ) - 1, by have := i.isLt; omega⟩ : Fin cd.d).castSucc))
    -- the OVERRIDE selector records the surviving `Gv = G − vᵢ` links (off the two split hinges):
    (hends_Gv : ∀ e u w, (G.removeVertex (cd.vtx i.castSucc)).IsLink e u w →
      (G.removeVertex (cd.vtx i.castSucc)).IsLink e (endsσρ₁ e).1 (endsσρ₁ e).2)
    -- the surviving-`Gv` support extensors are nonzero (dispatch-supplied off the candidate
    -- framework's general position, the `M₃`-`hne_Gva` analogue):
    (hne_Gv : ∀ e, (G.removeVertex (cd.vtx i.castSucc)).IsLink e (endsσρ₁ e).1 (endsσρ₁ e).2 →
      (PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx i.castSucc)) endsσρ₁
        (fun p => q (cd.shiftPerm i.castSucc p.1, p.2))).toBodyHinge.supportExtensor e ≠ 0)
    -- the transversal gate (the matched-candidate slot the Claim-6.12 discriminator fills, at the
    -- successor neighbour `a = vtx i.succ`, off the landed seed read `qρ(a,·) = q(vtx i.succ,·)`):
    (hLn : LinearIndependent ℝ ![(fun j => q (cd.vtx i.succ, j)), n'])
    -- the engine `hgab` is the `(a, v)` pair: the engine `b`-role seed reads at the SPLIT BODY `v`
    -- (`qρ(b,·) = q(v,·)`, `seedShift_pred_castSucc`), the cycle analogue of `M₃`'s `(c, a)` pair:
    (hgab : LinearIndependent ℝ
      ![(fun j => q (cd.vtx i.succ, j)), (fun j => q (cd.vtx i.castSucc, j))])
    (hρgate : ρ₀ (panelSupportExtensor (fun j => q (cd.vtx i.succ, j)) n') ≠ 0)
    -- the redundancy annihilation `hρe₀` at candidate `i`'s relabelled seed (landed,
    -- `interior_hρe₀_of_widening`):
    (hρe₀ : ρ₀ (panelSupportExtensor
          (fun j => (fun p => q (cd.shiftPerm i.castSucc p.1, p.2)) (cd.vtx i.succ, j))
          (fun j => (fun p => q (cd.shiftPerm i.castSucc p.1, p.2))
            (cd.vtx (⟨(i : ℕ) - 1, by have := i.isLt; omega⟩ : Fin cd.d).castSucc, j))) = 0)
    -- THE crux `±r` membership (landed `chainData_relabel_arm_hρGv`, §(4.95)/§(4.100)), at the
    -- candidate framework's HONEST base selector `ends₀` (the §(4.100) leaf re-target), honest
    -- engine — the eq.-(6.27) row-op decouples it from the gate:
    (hρGv : BodyHingeFramework.hingeRow (cd.vtx i.succ)
        (cd.vtx (⟨(i : ℕ) - 1, by have := i.isLt; omega⟩ : Fin cd.d).castSucc) (-ρ₀)
      ∈ Submodule.span ℝ (PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx i.castSucc))
        ends₀
        (fun p => q (cd.shiftPerm i.castSucc p.1, p.2))).toBodyHinge.rigidityRows)
    -- the base-split recording (LEAF-1's hypothesis; the (B′)-exposed discriminator conjunct
    -- `hrec'`): `ends₀` records every link of the `v₁`-base split — the input the swap-tolerant
    -- bridge `candidateEnds i ends₀ → endsσρ₁` consumes via the LEAF-1 supplier
    -- `candidateEnds_records_splitOff_isLink`.
    (hrec' : ∀ f x y, (G.splitOff (cd.vtx (⟨1, by have := i.isLt; omega⟩ : Fin cd.d).castSucc)
        (cd.vtx (⟨1, by have := i.isLt; omega⟩ : Fin cd.d).succ)
        (cd.vtx (⟨0, by have := i.isLt; omega⟩ : Fin cd.d).castSucc) cd.e₀).IsLink f x y →
      ends₀ f = (x, y) ∨ ends₀ f = (y, x))
    -- the bottom family (per-member relabelled, the `chainData_bottom_relabel` shape): the producer
    -- lands its genuine rows at the RELABEL-IMAGE selector `cd.candidateEnds i ends₀` (= `endsσρ`,
    -- pinned by the transport's `hsupp`, §(4.102)), NOT the honest `ends₀` (the `hρGv` slot below);
    -- the bridge to the engine override `endsσρ₁` is the swap-tolerant `congr_ends` (Probe (e)):
    {ιb : Type*} [Finite ιb] {w : ιb → Module.Dual ℝ (α → ScrewSpace k)}
    (hwcard : Nat.card ιb = screwDim k * (V(G).ncard - 2))
    (hw : LinearIndependent ℝ w)
    (hwmem : ∀ j, w j ∈ (PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx i.castSucc))
        (cd.candidateEnds i ends₀)
        (fun p => q (cd.shiftPerm i.castSucc p.1, p.2))).toBodyHinge.rigidityRows ∨
      ∃ ρ' : Module.Dual ℝ (ScrewSpace k),
        ρ' (panelSupportExtensor
            (fun j => (fun p => q (cd.shiftPerm i.castSucc p.1, p.2)) (cd.vtx i.succ, j))
            (fun j => (fun p => q (cd.shiftPerm i.castSucc p.1, p.2))
              (cd.vtx (⟨(i : ℕ) - 1, by have := i.isLt; omega⟩ : Fin cd.d).castSucc, j))) = 0 ∧
        w j = BodyHingeFramework.hingeRow (cd.vtx i.succ)
          (cd.vtx (⟨(i : ℕ) - 1, by have := i.isLt; omega⟩ : Fin cd.d).castSucc) ρ')
    (hdef : G.deficiency n = 0) :
    PanelHingeFramework.HasGenericFullRankRealization k n G := by
  classical
  haveI : Fintype α := Fintype.ofFinite α
  have h0i : 0 < (i : ℕ) := by omega
  -- The interior-split tuple `(v, a, b, e_a, e_b)` read off the `ChainData` accessors.
  set v := cd.vtx i.castSucc with hv
  set a := cd.vtx i.succ with ha
  set b := cd.vtx (⟨(i : ℕ) - 1, by omega⟩ : Fin cd.d).castSucc with hb
  set e_a := cd.edge i with hea
  set e_b := cd.edge ⟨(i : ℕ) - 1, by omega⟩ with heb
  -- The candidate seed `qρ` (the framework the §(4.100)-re-targeted landed leaves use, at `ends₀`).
  set qρ : α × Fin (k + 2) → ℝ := fun p => q (cd.shiftPerm i.castSucc p.1, p.2) with hqρ
  set Gv := G.removeVertex v with hGv
  -- The relabelled-seed reads at the engine roles `a`/`b` (the landed cycle `M₃`-`hqρc`/`hqρv`).
  have hqρa : (fun j => qρ (a, j)) = (fun j => q (a, j)) := cd.seedShift_succ_castSucc i q
  have hqρb : (fun j => qρ (b, j)) = (fun j => q (v, j)) := cd.seedShift_pred_castSucc h2i q
  -- The two chain edges, oriented *out of* the split body `v` (the accessors).
  have hlea : G.IsLink e_a v a := cd.isLink_succ_edge i
  have hleb : G.IsLink e_b v b := cd.isLink_pred_edge h0i
  -- Distinctness of the tuple, from `vtx_inj`/`edge_inj`.
  have heab : e_a ≠ e_b := (cd.pred_edge_ne h0i).symm
  have hvG : v ∈ V(G) := cd.vtx_mem _
  -- Surviving-`Gv`-link facts (shared with the M₃ arm's setup, off the `ChainData` accessors).
  have hvVc : v ∉ V(Gv) := cd.notMem_vertexSet_removeVertex_castSucc i
  have haVc : a ∈ V(Gv) := cd.succ_mem_vertexSet_removeVertex_castSucc i
  have hbVc : b ∈ V(Gv) := cd.pred_castSucc_mem_vertexSet_removeVertex_castSucc h0i
  have hleG : ∀ e u w, Gv.IsLink e u w → G.IsLink e u w :=
    fun e u w hlink => (Graph.removeVertex_isLink.mp hlink).1
  have hsplitG : ∀ e u w, G.IsLink e u w → e = e_a ∨ e = e_b ∨ Gv.IsLink e u w :=
    fun e u w hlink => cd.isLink_eq_succ_or_pred_or_removeVertex h0i hlink
  have hcard_Gv : V(Gv).ncard = V(G).ncard - 1 := by
    rw [hGv, Graph.vertexSet_removeVertex, Set.ncard_diff_singleton_of_mem hvG]
  have hVone : 1 ≤ V(Gv).ncard := (Set.ncard_pos (Set.toFinite _)).mpr ⟨a, haVc⟩
  have hVcard : V(G).ncard = V(Gv).ncard + 1 := by rw [hcard_Gv]; omega
  -- The two chain edges miss every `Gv`-link (each links the removed body `v ∉ V(Gv)`), so the
  -- override `endsσρ₁` agrees with the HONEST base selector `ends₀` there (Probe E2; the M₃
  -- `hGv_off`/`hends₁_off`).
  have hGv_off : ∀ {e u w}, Gv.IsLink e u w → e ≠ e_a ∧ e ≠ e_b := by
    intro e u w hlink
    rw [hGv, Graph.removeVertex_isLink] at hlink
    obtain ⟨hGlink, hunev, hwnev⟩ := hlink
    refine ⟨fun he => ?_, fun he => ?_⟩
    · subst he
      rcases hlea.eq_and_eq_or_eq_and_eq hGlink with ⟨hh, _⟩ | ⟨hh, _⟩
      · exact hunev hh.symm
      · exact hwnev hh.symm
    · subst he
      rcases hleb.eq_and_eq_or_eq_and_eq hGlink with ⟨hh, _⟩ | ⟨hh, _⟩
      · exact hunev hh.symm
      · exact hwnev hh.symm
  -- Bridge the HONEST-`ends₀`-stated bottom rows (`hρGv`/`hwmem`, where the §(4.100)-re-targeted
  -- leaves produce them) to the override `endsσρ₁` on `Gv`-links: the rigidity-row sets coincide
  -- where the two selectors agree (`rigidityRows_ofNormals_congr_ends`, the M₃ `hcongr`).
  have hcongr : (PanelHingeFramework.ofNormals Gv ends₀ qρ).toBodyHinge.rigidityRows
      = (PanelHingeFramework.ofNormals Gv endsσρ₁ qρ).toBodyHinge.rigidityRows :=
    PanelHingeFramework.rigidityRows_ofNormals_congr_ends qρ
      (fun e u w hlink => (hoff e (hGv_off hlink).1 (hGv_off hlink).2).symm)
  -- The bottom `hwmem` rows are at the RELABEL-IMAGE selector `candidateEnds i ends₀` (where the
  -- general-`d` producer `chainData_bottom_relabel` lands them, §(4.102)); bridge THOSE to the
  -- override `endsσρ₁` on `Gv`-links via the SWAP-tolerant congruence (the two selectors record
  -- each `Gv`-link only up to order — `candidateEnds` by LEAF-1, `endsσρ₁` by `hends_Gv`, (e)).
  have hcongr_swap :
      (PanelHingeFramework.ofNormals Gv (cd.candidateEnds i ends₀) qρ).toBodyHinge.rigidityRows
        = (PanelHingeFramework.ofNormals Gv endsσρ₁ qρ).toBodyHinge.rigidityRows :=
    PanelHingeFramework.rigidityRows_ofNormals_congr_ends_swap qρ <| by
      intro e u w hlink
      -- The `Gv`-link `e u w` is a genuine link of the candidate split (`u, w ≠ vᵢ`, and `e ≠ e₀`
      -- since `e ∈ E(G)` while `e₀ ∉ E(G)`); LEAF-1 then records it under `candidateEnds`.
      obtain ⟨hGlink, hunev, hwnev⟩ := Graph.removeVertex_isLink.mp hlink
      have hsplit : (G.splitOff v a b cd.e₀).IsLink e u w :=
        Graph.splitOff_isLink.mpr
          (Or.inl ⟨fun he => cd.e₀_fresh (he ▸ hGlink.edge_mem), hGlink, hunev, hwnev⟩)
      refine ⟨cd.candidateEnds_records_splitOff_isLink i (by omega) hrec' hsplit, ?_⟩
      -- `endsσρ₁` records the `Gv`-link up to order (`hends_Gv` gives `Gv.IsLink e (endsσρ₁ e).1
      -- (endsσρ₁ e).2`; compare with the original link via `eq_and_eq_or_eq_and_eq`).
      rcases hlink.eq_and_eq_or_eq_and_eq (hends_Gv e u w hlink) with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl (Prod.ext h1.symm h2.symm)
      · exact Or.inr (Prod.ext h2.symm h1.symm)
  -- The crux `±r` membership (at the HONEST `ends₀`, the §(4.100)-step-1 leaf) bridges through the
  -- EXACT `hcongr`; the bottom family bridges through the SWAP-tolerant `hcongr_swap`.
  have hρGv₁ : BodyHingeFramework.hingeRow a b (-ρ₀) ∈ Submodule.span ℝ
      (PanelHingeFramework.ofNormals Gv endsσρ₁ qρ).toBodyHinge.rigidityRows := by
    rw [← hcongr]; exact hρGv
  have hwmem₁ : ∀ j, w j ∈ (PanelHingeFramework.ofNormals Gv endsσρ₁ qρ).toBodyHinge.rigidityRows ∨
      ∃ ρ' : Module.Dual ℝ (ScrewSpace k),
        ρ' (panelSupportExtensor (fun j => qρ (a, j)) (fun j => qρ (b, j))) = 0 ∧
        w j = BodyHingeFramework.hingeRow a b ρ' := by
    intro j
    rcases hwmem j with hgen | hcand
    · exact Or.inl (by rw [← hcongr_swap]; exact hgen)
    · exact Or.inr hcand
  -- Re-index the honest engine at the `cd`-derived interior split tuple + override framework.
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
    -- the engine panel `C(qρ a, qρ b)` is defeq to `hρe₀`'s relabelled-seed panel; flip the `-ρ₀`.
    rw [LinearMap.neg_apply, neg_eq_zero]; exact hρe₀
  case hρGv =>
    -- `hingeRow a b (-ρ₀) ∈ span (ofNormals Gv endsσρ₁ qρ).rigidityRows` — the crux leaf, bridged
    -- from the raw `endsσρ` to the override `endsσρ₁` through `hcongr`.
    exact hρGv₁
  case hwcard => rw [hwcard, hcard_Gv, Nat.sub_sub]
  case hwmem => exact hwmem₁

/-- **CHAIN-2c-iii — the interior-arm geometry wrapper for the option-2 (separate `R(Gab)` bottom)
route** (`lem:case-III` general-`d`; Katoh–Tanigawa 2011 §6.4.2, Lemma 6.13 the interior per-`i`
arm; Phase 23e). The `ChainData`-indexed sibling of `chainData_split_realization`, routing the
interior degree-2 chain body `v := vtx i.castSucc` (`0 < i`) through the LEAF-SEPARM arm
`case_III_arm_realization_matrix_sep` (the option-2 disjoint-block cert, Phase 23d) **instead of**
the OLD literal-`0`-block `case_III_arm_realization`. This is the interior branch the general-`d`
dispatch (`chainData_dispatch`, LEAF-5) calls at a matched interior candidate `i`.

The wrapper supplies exactly the `Gv = G − vᵢ` framework geometry off the `ChainData` interior-split
accessors — split body `v := vtx i.castSucc`, successor neighbour `a := vtx i.succ` (chain edge
`e_a := edge i`), predecessor neighbour `b := vtx (i−1).castSucc` (chain edge `e_b := edge (i−1)`),
and the interior degree-2 closure (`deg_two_split`) saying those are `v`'s only two `G`-edges — the
identical setup `chainData_split_realization` derives (lines `1080`–`1201`), but ending in the
option-2 arm. The **disjoint-block obligations** (`corner`/`bottom` and their LI/membership/blind
facts `hcornerpin`/`hbotblind`/`hbotindep`/`hcornermem`/`hbotmem`, the counts `hm₁`/`hm₂`) and the
geometric gates (`hLn`/`hgab`) are carried as hypotheses — LEAF-4's outputs the dispatch threads in
(the corner from the §(4.35) corner leaves 1/2/3, the `R(Gab)` bottom from `hsplitGP`'s IH + the
cross-label bridge + L-span; `notes/Phase23-design.md` §I.8.24(4.10) LEAF-4/LEAF-5). The `ends`
slot is the re-inserted-hinge override `ends₁` (the `Function.update` selector the dispatch builds,
recording `e_a ↦ (v, a)`, `e_b ↦ (v, b)`; the W6b/disjoint-block rows are stated against it). No new
linear algebra, no `d = 3` content, no motive/IH change — pure `cd`-accessor + `Gv`-geometry wiring
on top of `case_III_arm_realization_matrix_sep`. No `\lean` pin (internal infra; the chain dispatch
carries the blueprint node). -/
theorem PanelHingeFramework.chainData_arm_realization_sep
    [DecidableEq α] [DecidableEq β] [Finite α] [Finite β]
    {G : Graph α β} {n : ℕ} (cd : G.ChainData n) (i : Fin cd.d) (hi : 0 < (i : ℕ))
    (hV3 : 3 ≤ V(G).ncard) (hSimple : G.Simple)
    {q : α × Fin (k + 2) → ℝ} (ends : β → α × α)
    -- the `ends` override records the two re-inserted chain hinges at the split body `v = vtx i`:
    (hends_ea : ends (cd.edge i) = (cd.vtx i.castSucc, cd.vtx i.succ))
    (hends_eb : ends (cd.edge ⟨(i : ℕ) - 1, by omega⟩) =
      (cd.vtx i.castSucc, cd.vtx (⟨(i : ℕ) - 1, by omega⟩ : Fin cd.d).castSucc))
    -- the split-off framework's general position (dispatch-supplied off the interior `hsplitGP`):
    (hgp : (PanelHingeFramework.ofNormals
        (G.splitOff (cd.vtx i.castSucc) (cd.vtx i.succ)
          (cd.vtx (⟨(i : ℕ) - 1, by omega⟩ : Fin cd.d).castSucc) cd.e₀) ends q).IsGeneralPosition)
    -- the `ends` selector records the surviving `Gv = G − vᵢ` links (off the two split hinges):
    (hends_Gv : ∀ e u w, (G.removeVertex (cd.vtx i.castSucc)).IsLink e u w →
      (G.removeVertex (cd.vtx i.castSucc)).IsLink e (ends e).1 (ends e).2)
    {n' : Fin (k + 2) → ℝ}
    (hLn : LinearIndependent ℝ ![(fun j => q (cd.vtx i.succ, j)), n'])
    (hgab : LinearIndependent ℝ
      ![(fun j => q (cd.vtx i.succ, j)),
        (fun j => q (cd.vtx (⟨(i : ℕ) - 1, by omega⟩ : Fin cd.d).castSucc, j))])
    -- the route-A OPTION-2 disjoint-block data (LEAF-4 outputs the dispatch threads in):
    {m₁ m₂ : Type*} [Fintype m₁] [Fintype m₂]
    (hm₁ : Fintype.card m₁ = screwDim k)
    (hm₂ : Fintype.card m₂ =
      screwDim k * (V(G.removeVertex (cd.vtx i.castSucc)).ncard - 1))
    {corner : m₁ → Module.Dual ℝ (α → ScrewSpace k)}
    {bottom : m₂ → Module.Dual ℝ (α → ScrewSpace k)}
    (hcornerpin : LinearIndependent ℝ
      (fun j : m₁ => (corner j).comp
        (LinearMap.single ℝ (fun _ : α => ScrewSpace k) (cd.vtx i.castSucc))))
    (hbotblind : ∀ (j : m₂) (S : α → ScrewSpace k) (x : ScrewSpace k),
      bottom j (Function.update S (cd.vtx i.castSucc) x) = bottom j S)
    (hbotindep : LinearIndependent ℝ bottom)
    (hcornermem : ∀ j, (corner j).comp
        (BodyHingeFramework.columnOp (k := k) (cd.castSucc_ne_succ i)).symm.toLinearMap ∈
      Submodule.span ℝ (PanelHingeFramework.caseIIICandidate G ends q (cd.edge i)
        (cd.edge ⟨(i : ℕ) - 1, by omega⟩) (fun j => q (cd.vtx i.succ, j)) n'
        (fun j => q (cd.vtx (⟨(i : ℕ) - 1, by omega⟩ : Fin cd.d).castSucc, j)) 0).rigidityRows)
    (hbotmem : ∀ j, bottom j ∈ Submodule.span ℝ
      (PanelHingeFramework.caseIIICandidate G ends q (cd.edge i)
        (cd.edge ⟨(i : ℕ) - 1, by omega⟩) (fun j => q (cd.vtx i.succ, j)) n'
        (fun j => q (cd.vtx (⟨(i : ℕ) - 1, by omega⟩ : Fin cd.d).castSucc, j)) 0).rigidityRows)
    (hdef : G.deficiency n = 0) :
    PanelHingeFramework.HasGenericFullRankRealization k n G := by
  classical
  haveI : Fintype α := Fintype.ofFinite α
  -- The interior-split tuple `(v, a, b, e_a, e_b)` read off the `ChainData` accessors.
  set v := cd.vtx i.castSucc with hv
  set a := cd.vtx i.succ with ha
  set b := cd.vtx (⟨(i : ℕ) - 1, by omega⟩ : Fin cd.d).castSucc with hb
  set e_a := cd.edge i with hea
  set e_b := cd.edge ⟨(i : ℕ) - 1, by omega⟩ with heb
  -- The two chain edges, oriented *out of* the split body `v` (the accessors).
  have hlea : G.IsLink e_a v a := cd.isLink_succ_edge i
  have hleb : G.IsLink e_b v b := cd.isLink_pred_edge hi
  -- The interior degree-2 closure at `v`: every `G`-edge at `v` is `e_a` or `e_b`.
  have hclv : ∀ e x, G.IsLink e v x → e = e_a ∨ e = e_b := cd.deg_two_split hi
  -- Distinctness of the tuple, from `vtx_inj`/`edge_inj`.
  have hba : b ≠ a := (cd.succ_ne_pred_castSucc hi).symm
  have heab : e_a ≠ e_b := (cd.pred_edge_ne hi).symm
  have hva : v ≠ a := cd.castSucc_ne_succ i
  haveI hGloop : G.Loopless := hSimple.toLoopless
  set Gv := G.removeVertex v with hGv
  haveI : Gv.Loopless := hGloop.mono (hGv ▸ Graph.removeVertex_le G v)
  -- Surviving-`Gv`-link facts shared with `chainData_split_realization`'s setup.
  have hvVc : v ∉ V(Gv) := by rw [hGv, Graph.vertexSet_removeVertex]; exact fun h => h.2 rfl
  have haVc : a ∈ V(Gv) := by
    rw [hGv, Graph.vertexSet_removeVertex]; exact ⟨cd.vtx_mem _, (cd.castSucc_ne_succ i).symm⟩
  have hbVc : b ∈ V(Gv) := by
    rw [hGv, Graph.vertexSet_removeVertex]
    exact ⟨cd.vtx_mem _, (cd.castSucc_ne_pred_castSucc hi).symm⟩
  have hleG : ∀ e u w, Gv.IsLink e u w → G.IsLink e u w := by
    intro e u w hlink; rw [hGv, Graph.removeVertex_isLink] at hlink; exact hlink.1
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
  have hvG : v ∈ V(G) := cd.vtx_mem _
  have hVone : 1 ≤ V(Gv).ncard := by
    rw [hGv, Graph.vertexSet_removeVertex, Set.ncard_diff_singleton_of_mem hvG]; omega
  have hVcard : V(G).ncard = V(Gv).ncard + 1 := by
    rw [hGv, Graph.vertexSet_removeVertex, Set.ncard_diff_singleton_of_mem hvG]; omega
  -- `hne_Gv`: the surviving-`Gv` support extensors are nonzero, from the split realization's
  -- general position (the normals are LI on every distinct pair).
  have hne_Gv : ∀ e, Gv.IsLink e (ends e).1 (ends e).2 →
      (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge.supportExtensor e ≠ 0 := by
    intro e hlink
    apply PanelHingeFramework.supportExtensor_ne_zero_of_isGeneralPosition
    · intro x y hxy
      rw [PanelHingeFramework.ofNormals_normal, PanelHingeFramework.ofNormals_normal]
      have := hgp x y hxy
      rwa [PanelHingeFramework.ofNormals_normal, PanelHingeFramework.ofNormals_normal] at this
    · rw [PanelHingeFramework.ofNormals_ends]; exact hlink.ne
  exact PanelHingeFramework.case_III_arm_realization_matrix_sep (k := k) G Gv ends
    (q := q) (v := v) (a := a) (b := b) (e_a := e_a) (e_b := e_b) (n' := n')
    hvVc haVc hbVc hva hlea hleb hends_ea hends_eb heab hleG hsplitG hends_Gv hne_Gv
    hVone hVcard hLn hgab hm₁ hm₂ hcornerpin hbotblind hbotindep hcornermem hbotmem hdef

/-- **D-CAN-3b — the interior-arm geometry wrapper for the (D-canonical) literal-IH-bottom
`_zero₁₂`-cert route** (`lem:case-III` general-`d`; Katoh–Tanigawa 2011 §6.4.2, Lemma 6.13 the
interior per-`i` arm; Phase 23f, `notes/Phase23-design.md` §(4.72.3)). The `ChainData`-indexed
sibling of `chainData_arm_realization_sep`, routing the interior degree-2 chain body
`v := vtx i.castSucc` (`0 < i`) through the row-op matrix-data arm
`case_III_arm_realization_rowOp` (the A3-transposed `_zero₁₂` cert with the literal IH bottom,
fed D-CAN-3a's `hD`) **instead of** the span-membership disjoint-block arm
`case_III_arm_realization_matrix_sep`.

The `_zero₁₂` route is the (D-canonical) escape (`notes/Phase23-design.md` §(4.71)/(4.72)): under
D-CAN-1's support-extensor-keyed canonical `blockBasisOn`, D-CAN-2's literal-`Matrix` bottom bridge
`submatrix_columnOp_toBlocks₂₂_eq_Gab` rewrites the operated `mixedBottom` block to the literal IH
matrix `R(Gab)`'s `a`-shifted rows, so the bottom-block full-rank `hD`
(`linearIndependent_toBlocks₂₂_row_Gab_of_finrank_eq`, D-CAN-3a) is the IH `R(Gab)` full rank read
off a *RANK* fact — never a span membership (the §(4.29) override-discriminator gate never forms),
the wall §(4.70) found under the opaque basis dissolved.

The wrapper supplies exactly the `Gv = G − vᵢ` framework geometry off the `ChainData` interior-split
accessors — split body `v := vtx i.castSucc`, successor neighbour `a := vtx i.succ` (chain edge
`e_a := edge i`), predecessor neighbour `b := vtx (i−1).castSucc` (chain edge `e_b := edge (i−1)`),
and the interior degree-2 closure (`deg_two_split`) — the **identical** setup
`chainData_arm_realization_sep` (and `chainData_split_realization`) derives, ending instead in the
row-op arm. The **row-op (4b″) matrix block data** (`re`/`hre`/`L₀`/`hM'eq`/`hB`/`hA`/`hD` and the
counts `hm₁`/`hm₂`) and the candidate framework's edge-restricted facts (`hgp`/`hends`) + geometric
gates (`hLn`/`hgab`) are carried as hypotheses — the dispatch threads them in (the corner `hA` from
`corner_hA_zero₁₂_of_gate` fed the discriminator gate; the bottom `hD` from D-CAN-3a fed the IH
`hsplitGP` full rank via the cross-framework `re₂`/`hj`/`hsupp`, all GATE-FREE per §(4.72.1)). The
`ends` slot is the re-inserted-hinge override the dispatch builds (recording `e_a ↦ (v, a)`,
`e_b ↦ (v, b)`). No new linear algebra, no `d = 3` content, no motive/IH change — pure `cd`-accessor
+ `Gv`-geometry wiring on top of `case_III_arm_realization_rowOp`. No `\lean` pin (internal infra;
the chain dispatch carries the blueprint node). -/
theorem PanelHingeFramework.chainData_arm_realization_zero₁₂
    [DecidableEq α] [DecidableEq β] [Fintype α] [Finite β]
    {G : Graph α β} {n : ℕ} (cd : G.ChainData n) (i : Fin cd.d) (hi : 0 < (i : ℕ))
    (hV3 : 3 ≤ V(G).ncard)
    {q : α × Fin (k + 2) → ℝ} (ends : β → α × α)
    -- the `ends` override records the two re-inserted chain hinges at the split body `v = vtx i`:
    (hends_ea : ends (cd.edge i) = (cd.vtx i.castSucc, cd.vtx i.succ))
    (hends_eb : ends (cd.edge ⟨(i : ℕ) - 1, by omega⟩) =
      (cd.vtx i.castSucc, cd.vtx (⟨(i : ℕ) - 1, by omega⟩ : Fin cd.d).castSucc))
    {n' : Fin (k + 2) → ℝ}
    (hLn : LinearIndependent ℝ ![(fun j => q (cd.vtx i.succ, j)), n'])
    (hgab : LinearIndependent ℝ
      ![(fun j => q (cd.vtx i.succ, j)),
        (fun j => q (cd.vtx (⟨(i : ℕ) - 1, by omega⟩ : Fin cd.d).castSucc, j))])
    -- the candidate framework's edge-restricted general-position + link-recording hypotheses:
    (hgp : ∀ e ∈ G.edgeSet,
      (PanelHingeFramework.caseIIICandidate G ends q (cd.edge i)
        (cd.edge ⟨(i : ℕ) - 1, by omega⟩) (fun j => q (cd.vtx i.succ, j)) n'
        (fun j => q (cd.vtx (⟨(i : ℕ) - 1, by omega⟩ : Fin cd.d).castSucc, j)) 0).supportExtensor
          e ≠ 0)
    (hends : ∀ e ∈ G.edgeSet, G.IsLink e (ends e).1 (ends e).2)
    -- the `ends` selector records the surviving `Gv = G − vᵢ` links + their nonzero support
    -- extensors (the dispatch supplies these off the interior `hsplitGP` general position):
    (hends_Gv : ∀ e u w, (G.removeVertex (cd.vtx i.castSucc)).IsLink e u w →
      (G.removeVertex (cd.vtx i.castSucc)).IsLink e (ends e).1 (ends e).2)
    (hne_Gv : ∀ e, (G.removeVertex (cd.vtx i.castSucc)).IsLink e (ends e).1 (ends e).2 →
      (PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx i.castSucc)) ends
        q).toBodyHinge.supportExtensor e ≠ 0)
    -- the row-op (4b″) matrix block data (the chain dispatch discharges these next):
    {m₁ m₂ : Type*} [Fintype m₁] [Fintype m₂]
    (hm₁ : Fintype.card m₁ = screwDim k)
    (hm₂ : Fintype.card m₂ =
      screwDim k * (V(G.removeVertex (cd.vtx i.castSucc)).ncard - 1))
    (re : m₁ ⊕ m₂ → ({e // e ∈ (PanelHingeFramework.caseIIICandidate G ends q (cd.edge i)
      (cd.edge ⟨(i : ℕ) - 1, by omega⟩) (fun j => q (cd.vtx i.succ, j)) n'
      (fun j => q (cd.vtx (⟨(i : ℕ) - 1, by omega⟩ : Fin cd.d).castSucc, j)) 0).graph.edgeSet}
        × Fin (screwDim k - 1)))
    (hre : Function.Injective re)
    (L₀ : Matrix m₁ m₂ ℝ)
    {A : Matrix m₁ ({body : α // body = cd.vtx i.castSucc}
        × Fin (Module.finrank ℝ (ScrewSpace k))) ℝ}
    {B : Matrix m₁ ({body : α // body ≠ cd.vtx i.castSucc}
        × Fin (Module.finrank ℝ (ScrewSpace k))) ℝ}
    {C : Matrix m₂ ({body : α // body = cd.vtx i.castSucc}
        × Fin (Module.finrank ℝ (ScrewSpace k))) ℝ}
    {D : Matrix m₂ ({body : α // body ≠ cd.vtx i.castSucc}
        × Fin (Module.finrank ℝ (ScrewSpace k))) ℝ}
    (hM'eq :
      ((PanelHingeFramework.caseIIICandidate G ends q (cd.edge i)
            (cd.edge ⟨(i : ℕ) - 1, by omega⟩) (fun j => q (cd.vtx i.succ, j)) n'
            (fun j => q (cd.vtx (⟨(i : ℕ) - 1, by omega⟩ : Fin cd.d).castSucc, j))
            0).rigidityMatrixEdge ends hgp
          * (LinearMap.toMatrix' (prodColumnOpEquiv (k := k) (α := α)
              (BodyHingeFramework.columnOp (k := k)
                (cd.castSucc_ne_succ i)).symm).toLinearMap).transpose).submatrix
        re (columnSplit (k := k) (cd.vtx i.castSucc)).symm
        = Matrix.fromBlocks A B C D)
    (hB : B = L₀ * D)
    (hA : LinearIndependent ℝ (A - L₀ * C).row)
    (hD : LinearIndependent ℝ D.row)
    (hdef : G.deficiency n = 0) :
    PanelHingeFramework.HasGenericFullRankRealization k n G := by
  classical
  -- The interior-split tuple `(v, a, b, e_a, e_b)` read off the `ChainData` accessors. We do
  -- **not** `set`-fold: folding the `re`/`hM'eq` candidate types is both expensive and breaks the
  -- syntactic match with `case_III_arm_realization_rowOp`'s expected type. The final call passes
  -- the literal `cd`-forms and the geometry `have`s are stated against them, so unification pins
  -- `v/a/b/e_a/e_b` from the carried `re`/`hM'eq`.
  have hlea : G.IsLink (cd.edge i) (cd.vtx i.castSucc) (cd.vtx i.succ) := cd.isLink_succ_edge i
  have hleb : G.IsLink (cd.edge ⟨(i : ℕ) - 1, by omega⟩) (cd.vtx i.castSucc)
      (cd.vtx (⟨(i : ℕ) - 1, by omega⟩ : Fin cd.d).castSucc) := cd.isLink_pred_edge hi
  -- The interior degree-2 closure at `v`: every `G`-edge at `v` is `e_a` or `e_b`.
  have hclv : ∀ e x, G.IsLink e (cd.vtx i.castSucc) x →
      e = cd.edge i ∨ e = cd.edge ⟨(i : ℕ) - 1, by omega⟩ := cd.deg_two_split hi
  -- Distinctness of the tuple, from `vtx_inj`/`edge_inj`.
  have heab : cd.edge i ≠ cd.edge ⟨(i : ℕ) - 1, by omega⟩ := (cd.pred_edge_ne hi).symm
  have hva : cd.vtx i.castSucc ≠ cd.vtx i.succ := cd.castSucc_ne_succ i
  -- Surviving-`Gv`-link facts shared with `chainData_split_realization`'s setup.
  have hvVc : cd.vtx i.castSucc ∉ V(G.removeVertex (cd.vtx i.castSucc)) := by
    rw [Graph.vertexSet_removeVertex]; exact fun h => h.2 rfl
  have haVc : cd.vtx i.succ ∈ V(G.removeVertex (cd.vtx i.castSucc)) := by
    rw [Graph.vertexSet_removeVertex]; exact ⟨cd.vtx_mem _, (cd.castSucc_ne_succ i).symm⟩
  have hbVc : cd.vtx (⟨(i : ℕ) - 1, by omega⟩ : Fin cd.d).castSucc ∈
      V(G.removeVertex (cd.vtx i.castSucc)) := by
    rw [Graph.vertexSet_removeVertex]
    exact ⟨cd.vtx_mem _, (cd.castSucc_ne_pred_castSucc hi).symm⟩
  have hleG : ∀ e u w, (G.removeVertex (cd.vtx i.castSucc)).IsLink e u w → G.IsLink e u w := by
    intro e u w hlink; rw [Graph.removeVertex_isLink] at hlink; exact hlink.1
  have hsplitG : ∀ e u w, G.IsLink e u w → e = cd.edge i ∨ e = cd.edge ⟨(i : ℕ) - 1, by omega⟩ ∨
      (G.removeVertex (cd.vtx i.castSucc)).IsLink e u w := by
    intro e u w hlink
    by_cases hu : u = cd.vtx i.castSucc
    · subst u; rcases hclv e w hlink with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
    · by_cases hw : w = cd.vtx i.castSucc
      · subst w; rcases hclv e u hlink.symm with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (by rw [Graph.removeVertex_isLink]; exact ⟨hlink, hu, hw⟩))
  have hvG : cd.vtx i.castSucc ∈ V(G) := cd.vtx_mem _
  have hVone : 1 ≤ V(G.removeVertex (cd.vtx i.castSucc)).ncard := by
    rw [Graph.vertexSet_removeVertex, Set.ncard_diff_singleton_of_mem hvG]; omega
  have hVcard : V(G).ncard = V(G.removeVertex (cd.vtx i.castSucc)).ncard + 1 := by
    rw [Graph.vertexSet_removeVertex, Set.ncard_diff_singleton_of_mem hvG]; omega
  exact PanelHingeFramework.case_III_arm_realization_rowOp (k := k) G
    (G.removeVertex (cd.vtx i.castSucc)) ends (q := q)
    hvVc haVc hbVc hva hlea hleb hends_ea hends_eb heab hleG hsplitG hends_Gv hne_Gv
    hVone hVcard hLn hgab hgp hends hm₁ hm₂ re hre L₀ hM'eq hB hA hD hdef

/-- **D-CAN-4 route (D) sub-commit 3 — the AUGMENTED interior-arm geometry wrapper for the
(D-canonical) literal-IH-bottom `_aug`-cert route** (`lem:case-III` general-`d`; Katoh–Tanigawa 2011
§6.4.2, Lemma 6.13 the interior per-`i` arm with KT eq. (6.66)'s genuine `±r` row; Phase 23f,
`notes/Phase23-design.md` §(4.78), `notes/Phase23f.md` route (D) sub-commit 3). The augmented
sibling of `chainData_arm_realization_zero₁₂`: it routes the interior degree-2 chain body
`v := vtx i.castSucc` (`0 < i`) through the **augmented** row-op arm
`case_III_arm_realization_aug` — the augmented A3-transposed `_aug` cert carrying KT eq. (6.66)'s
genuine `±r` row in the single `inr ()` slot of `rigidityMatrixEdgeAug`, sourced from the genuine
functional `rRow` (the dispatch's `hingeRow b v ρ₀`) with its honest-span membership `hr` —
**instead of** the un-augmented `case_III_arm_realization_rowOp`.

Route (D) (`notes/Phase23-design.md` §(4.78)) fires the LANDED `_aug` ladder on the D-canonical
PIN-ZERO bottom: under the literal-IH `R(Gab)` bottom there is no `v`-incident `e_b`-fill, so the
operated bottom `C = toBlocks₂₁ = 0` and the operated corner `A − L₀·C = A` is the bare augmented
corner family `[blockBasisOn(e_a); −ρ₀]` (D3/D4, `Concrete.lean`), row-LI from the discriminator's
NONZERO gate alone (`corner_hA_aug_zero₁₂_of_gate`). This is the combination §(4.67)/§(4.68) never
tested — they blocked `_aug` under the `mixedBottom` (`C ≠ 0`); the D-canonical bottom post-dates
them (§(4.71)). No override-gate re-entry: the gate `hρe₀` + the perp `hr` are the discriminator's
DIRECT-`q` outputs.

The wrapper supplies the **identical** `Gv = G − vᵢ` framework geometry as
`chainData_arm_realization_zero₁₂` off the `ChainData` interior-split accessors — split body
`v := vtx i.castSucc`, successor neighbour `a := vtx i.succ` (chain edge `e_a := edge i`),
predecessor neighbour `b := vtx (i−1)` (chain edge `e_b := edge (i−1)`), and the interior degree-2
closure (`deg_two_split`). The **augmented** row-op (4b″) block data
(`re`/`hre`/`L₀`/`rRow`/`hr`/`hM'eq`/`hB`/`hA`/`hD` and the counts `hm₁`/`hm₂`) and the candidate
framework's edge-restricted facts (`hgp`/`hends`) + geometric gates (`hLn`/`hgab`) are carried as
hypotheses — the chain dispatch threads them in (`rRow := hingeRow b v ρ₀` + `hr` via
`hingeRow_mem_caseIIICandidate_rigidityRows_reproduced`; the corner `hA` from D3
`corner_hA_aug_zero₁₂_of_gate`; the bottom `hD` from D-CAN-3a). The `ends` slot is the
re-inserted-hinge override the dispatch builds (recording `e_a ↦ (v, a)`, `e_b ↦ (v, b)`). No new
linear algebra, no `d = 3` content, no motive/IH change — pure `cd`-accessor + `Gv`-geometry wiring
on top of `case_III_arm_realization_aug`. No `\lean` pin (internal infra; the chain dispatch carries
the blueprint node). -/
theorem PanelHingeFramework.chainData_arm_realization_aug_zero₁₂
    [DecidableEq α] [DecidableEq β] [Fintype α] [Finite β]
    {G : Graph α β} {n : ℕ} (cd : G.ChainData n) (i : Fin cd.d) (hi : 0 < (i : ℕ))
    (hV3 : 3 ≤ V(G).ncard)
    {q : α × Fin (k + 2) → ℝ} (ends : β → α × α)
    -- the `ends` override records the two re-inserted chain hinges at the split body `v = vtx i`:
    (hends_ea : ends (cd.edge i) = (cd.vtx i.castSucc, cd.vtx i.succ))
    (hends_eb : ends (cd.edge ⟨(i : ℕ) - 1, by omega⟩) =
      (cd.vtx i.castSucc, cd.vtx (⟨(i : ℕ) - 1, by omega⟩ : Fin cd.d).castSucc))
    {n' : Fin (k + 2) → ℝ}
    (hLn : LinearIndependent ℝ ![(fun j => q (cd.vtx i.succ, j)), n'])
    (hgab : LinearIndependent ℝ
      ![(fun j => q (cd.vtx i.succ, j)),
        (fun j => q (cd.vtx (⟨(i : ℕ) - 1, by omega⟩ : Fin cd.d).castSucc, j))])
    -- the candidate framework's edge-restricted general-position + link-recording hypotheses:
    (hgp : ∀ e ∈ G.edgeSet,
      (PanelHingeFramework.caseIIICandidate G ends q (cd.edge i)
        (cd.edge ⟨(i : ℕ) - 1, by omega⟩) (fun j => q (cd.vtx i.succ, j)) n'
        (fun j => q (cd.vtx (⟨(i : ℕ) - 1, by omega⟩ : Fin cd.d).castSucc, j)) 0).supportExtensor
          e ≠ 0)
    (hends : ∀ e ∈ G.edgeSet, G.IsLink e (ends e).1 (ends e).2)
    -- the `ends` selector records the surviving `Gv = G − vᵢ` links + their nonzero support
    -- extensors (the dispatch supplies these off the interior `hsplitGP` general position):
    (hends_Gv : ∀ e u w, (G.removeVertex (cd.vtx i.castSucc)).IsLink e u w →
      (G.removeVertex (cd.vtx i.castSucc)).IsLink e (ends e).1 (ends e).2)
    (hne_Gv : ∀ e, (G.removeVertex (cd.vtx i.castSucc)).IsLink e (ends e).1 (ends e).2 →
      (PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx i.castSucc)) ends
        q).toBodyHinge.supportExtensor e ≠ 0)
    -- the augmented row-op (4b″) matrix block data (the chain dispatch discharges these next):
    {m₁ m₂ : Type*} [Fintype m₁] [Fintype m₂]
    (hm₁ : Fintype.card m₁ = screwDim k)
    (hm₂ : Fintype.card m₂ =
      screwDim k * (V(G.removeVertex (cd.vtx i.castSucc)).ncard - 1))
    (re : m₁ ⊕ m₂ → (({e // e ∈ (PanelHingeFramework.caseIIICandidate G ends q (cd.edge i)
      (cd.edge ⟨(i : ℕ) - 1, by omega⟩) (fun j => q (cd.vtx i.succ, j)) n'
      (fun j => q (cd.vtx (⟨(i : ℕ) - 1, by omega⟩ : Fin cd.d).castSucc, j)) 0).graph.edgeSet}
        × Fin (screwDim k - 1)) ⊕ Unit))
    (hre : Function.Injective re)
    (L₀ : Matrix m₁ m₂ ℝ)
    -- the genuine `±r` functional sourcing the augmented `inr ()` row, in the honest span:
    {rRow : Module.Dual ℝ (α → ScrewSpace k)}
    (hr : rRow ∈ Submodule.span ℝ
      (PanelHingeFramework.caseIIICandidate G ends q (cd.edge i)
        (cd.edge ⟨(i : ℕ) - 1, by omega⟩) (fun j => q (cd.vtx i.succ, j)) n'
        (fun j => q (cd.vtx (⟨(i : ℕ) - 1, by omega⟩ : Fin cd.d).castSucc, j)) 0).rigidityRows)
    {A : Matrix m₁ ({body : α // body = cd.vtx i.castSucc}
        × Fin (Module.finrank ℝ (ScrewSpace k))) ℝ}
    {B : Matrix m₁ ({body : α // body ≠ cd.vtx i.castSucc}
        × Fin (Module.finrank ℝ (ScrewSpace k))) ℝ}
    {C : Matrix m₂ ({body : α // body = cd.vtx i.castSucc}
        × Fin (Module.finrank ℝ (ScrewSpace k))) ℝ}
    {D : Matrix m₂ ({body : α // body ≠ cd.vtx i.castSucc}
        × Fin (Module.finrank ℝ (ScrewSpace k))) ℝ}
    (hM'eq :
      ((PanelHingeFramework.caseIIICandidate G ends q (cd.edge i)
            (cd.edge ⟨(i : ℕ) - 1, by omega⟩) (fun j => q (cd.vtx i.succ, j)) n'
            (fun j => q (cd.vtx (⟨(i : ℕ) - 1, by omega⟩ : Fin cd.d).castSucc, j))
            0).rigidityMatrixEdgeAug ends hgp rRow
          * (LinearMap.toMatrix' (prodColumnOpEquiv (k := k) (α := α)
              (BodyHingeFramework.columnOp (k := k)
                (cd.castSucc_ne_succ i)).symm).toLinearMap).transpose).submatrix
        re (columnSplit (k := k) (cd.vtx i.castSucc)).symm
        = Matrix.fromBlocks A B C D)
    (hB : B = L₀ * D)
    (hA : LinearIndependent ℝ (A - L₀ * C).row)
    (hD : LinearIndependent ℝ D.row)
    (hdef : G.deficiency n = 0) :
    PanelHingeFramework.HasGenericFullRankRealization k n G := by
  classical
  -- The interior-split tuple `(v, a, b, e_a, e_b)` read off the `ChainData` accessors. As in
  -- `chainData_arm_realization_zero₁₂` we do **not** `set`-fold: the final call passes the literal
  -- `cd`-forms and the geometry `have`s are stated against them, so unification pins
  -- `v/a/b/e_a/e_b` from the carried `re`/`hM'eq`/`hr`.
  have hlea : G.IsLink (cd.edge i) (cd.vtx i.castSucc) (cd.vtx i.succ) := cd.isLink_succ_edge i
  have hleb : G.IsLink (cd.edge ⟨(i : ℕ) - 1, by omega⟩) (cd.vtx i.castSucc)
      (cd.vtx (⟨(i : ℕ) - 1, by omega⟩ : Fin cd.d).castSucc) := cd.isLink_pred_edge hi
  -- The interior degree-2 closure at `v`: every `G`-edge at `v` is `e_a` or `e_b`.
  have hclv : ∀ e x, G.IsLink e (cd.vtx i.castSucc) x →
      e = cd.edge i ∨ e = cd.edge ⟨(i : ℕ) - 1, by omega⟩ := cd.deg_two_split hi
  -- Distinctness of the tuple, from `vtx_inj`/`edge_inj`.
  have heab : cd.edge i ≠ cd.edge ⟨(i : ℕ) - 1, by omega⟩ := (cd.pred_edge_ne hi).symm
  have hva : cd.vtx i.castSucc ≠ cd.vtx i.succ := cd.castSucc_ne_succ i
  -- Surviving-`Gv`-link facts shared with `chainData_split_realization`'s setup.
  have hvVc : cd.vtx i.castSucc ∉ V(G.removeVertex (cd.vtx i.castSucc)) := by
    rw [Graph.vertexSet_removeVertex]; exact fun h => h.2 rfl
  have haVc : cd.vtx i.succ ∈ V(G.removeVertex (cd.vtx i.castSucc)) := by
    rw [Graph.vertexSet_removeVertex]; exact ⟨cd.vtx_mem _, (cd.castSucc_ne_succ i).symm⟩
  have hbVc : cd.vtx (⟨(i : ℕ) - 1, by omega⟩ : Fin cd.d).castSucc ∈
      V(G.removeVertex (cd.vtx i.castSucc)) := by
    rw [Graph.vertexSet_removeVertex]
    exact ⟨cd.vtx_mem _, (cd.castSucc_ne_pred_castSucc hi).symm⟩
  have hleG : ∀ e u w, (G.removeVertex (cd.vtx i.castSucc)).IsLink e u w → G.IsLink e u w := by
    intro e u w hlink; rw [Graph.removeVertex_isLink] at hlink; exact hlink.1
  have hsplitG : ∀ e u w, G.IsLink e u w → e = cd.edge i ∨ e = cd.edge ⟨(i : ℕ) - 1, by omega⟩ ∨
      (G.removeVertex (cd.vtx i.castSucc)).IsLink e u w := by
    intro e u w hlink
    by_cases hu : u = cd.vtx i.castSucc
    · subst u; rcases hclv e w hlink with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
    · by_cases hw : w = cd.vtx i.castSucc
      · subst w; rcases hclv e u hlink.symm with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (by rw [Graph.removeVertex_isLink]; exact ⟨hlink, hu, hw⟩))
  have hvG : cd.vtx i.castSucc ∈ V(G) := cd.vtx_mem _
  have hVone : 1 ≤ V(G.removeVertex (cd.vtx i.castSucc)).ncard := by
    rw [Graph.vertexSet_removeVertex, Set.ncard_diff_singleton_of_mem hvG]; omega
  have hVcard : V(G).ncard = V(G.removeVertex (cd.vtx i.castSucc)).ncard + 1 := by
    rw [Graph.vertexSet_removeVertex, Set.ncard_diff_singleton_of_mem hvG]; omega
  exact PanelHingeFramework.case_III_arm_realization_aug (k := k) G
    (G.removeVertex (cd.vtx i.castSucc)) ends (q := q)
    hvVc haVc hbVc hva hlea hleb hends_ea hends_eb heab hleG hsplitG hends_Gv hne_Gv
    hVone hVcard hLn hgab hgp hends hm₁ hm₂ re hre L₀ hr hM'eq hB hA hD hdef

/-- **The genuine-`ofNormals` interior-arm geometry spine (the (D-substitution) `cd`-taking arm)**
(`lem:case-III` general-`d`; Katoh–Tanigawa 2011 §6.4.2, Lemma 6.13 the interior per-`i` arm with KT
eq. (6.66)'s genuine `±r` row; Phase 23f, Gap B, `notes/Phase23-design.md` §(4.89.4),
`notes/Phase23f.md` *Hand-off*). The **`_ofNormals` analog** of
`chainData_arm_realization_aug_zero₁₂`: it routes the interior degree-2 chain body
`v := vtx i.castSucc` through the genuine-framework augmented arm
`case_III_arm_realization_aug_ofNormals` — the (D-substitution) candidate is the literal panel-hinge
framework `F = ofNormals G ends q` (KT 6.59, `v` re-inserted at its genuine seed), with NO
`caseIIICandidate` extensor override, so the augmented `±r` row is the genuine chain-edge
`(vᵢ vᵢ₊₁)`-row and its honest-span membership `hr` is the LANDED S1 leaf
`hingeRow_mem_ofNormals_rigidityRows_chainEdge`.

The S4 arm `case_III_arm_realization_aug_ofNormals` is much simpler than the override
`case_III_arm_realization_aug` (its rank-to-realization tail
`case_III_realization_of_rank_ofNormals` needs no `Gv/v/a/b/e_a/e_b` chain-arm machinery and no W6f
shear, §(4.86)), so this spine is correspondingly thin: it supplies only the split body
`v := vtx i.castSucc`, its successor neighbour `a := vtx i.succ`, the deleted-vertex graph
`Gv := G − v`, the distinctness `hva` (`castSucc_ne_succ`), and the `removeVertex` cardinality facts
(`hVone`/`hVcard`), then fires the arm with the augmented row-op (4b″) block data
(`re`/`hre`/`L₀`/`rRow`/`hr`/`hM'eq`/`hB`/`hA`/`hD` + the `hm₁`/`hm₂` counts) and the framework
facts (`hgp`/`hends`) carried as hypotheses. The chain dispatch
(`chainData_dispatch`, the `Fin cd.d` router) threads those in — `rRow := hingeRow (vtx i.castSucc)
(vtx i.succ) ρ₀` with `hr` via the S1 leaf; the corner `hA` via §(4.89.5)'s
`corner_hA_aug_zero₁₂_of_gate` composition (`C = 0` pin-zero, `L₀` unused); the corner `hB`/`L₀` via
the (5c) `submatrix_columnOp_toBlocks₁₂_aug_eq_mul_toBlocks₂₂`; the bottom `re`/`hre`/`hD` via the
(5e) `exists_aug_bottom_blockData_of_Gab`; `hM'eq` the trivial `(fromBlocks_toBlocks _).symm` block
read. No new linear algebra, no `d = 3` content, no motive/IH change — pure `cd`-accessor +
`Gv`-geometry wiring on top of `case_III_arm_realization_aug_ofNormals`. No `\lean` pin (internal
infra; the chain dispatch carries the blueprint node). -/
theorem PanelHingeFramework.chainData_arm_realization_ofNormals
    [DecidableEq α] [Fintype α] [Finite β]
    {G : Graph α β} {n : ℕ} (cd : G.ChainData n) (i : Fin cd.d)
    {q : α × Fin (k + 2) → ℝ} (ends : β → α × α)
    -- the genuine framework's edge-restricted general-position + link-recording hypotheses:
    (hgp : ∀ e ∈ G.edgeSet,
      (PanelHingeFramework.ofNormals G ends q).toBodyHinge.supportExtensor e ≠ 0)
    (hends : ∀ e u w, G.IsLink e u w → G.IsLink e (ends e).1 (ends e).2)
    -- the augmented row-op (4b″) matrix block data (the chain dispatch discharges these next):
    {m₁ m₂ : Type*} [Fintype m₁] [Fintype m₂]
    (hm₁ : Fintype.card m₁ = screwDim k)
    (hm₂ : Fintype.card m₂ =
      screwDim k * (V(G.removeVertex (cd.vtx i.castSucc)).ncard - 1))
    (re : m₁ ⊕ m₂ →
      (({e // e ∈ (PanelHingeFramework.ofNormals G ends q).toBodyHinge.graph.edgeSet}
        × Fin (screwDim k - 1)) ⊕ Unit))
    (hre : Function.Injective re)
    (L₀ : Matrix m₁ m₂ ℝ)
    -- the genuine `±r` functional sourcing the augmented `inr ()` row, in the honest span:
    {rRow : Module.Dual ℝ (α → ScrewSpace k)}
    (hr : rRow ∈ Submodule.span ℝ
      (PanelHingeFramework.ofNormals G ends q).toBodyHinge.rigidityRows)
    {A : Matrix m₁ ({body : α // body = cd.vtx i.castSucc}
        × Fin (Module.finrank ℝ (ScrewSpace k))) ℝ}
    {B : Matrix m₁ ({body : α // body ≠ cd.vtx i.castSucc}
        × Fin (Module.finrank ℝ (ScrewSpace k))) ℝ}
    {C : Matrix m₂ ({body : α // body = cd.vtx i.castSucc}
        × Fin (Module.finrank ℝ (ScrewSpace k))) ℝ}
    {D : Matrix m₂ ({body : α // body ≠ cd.vtx i.castSucc}
        × Fin (Module.finrank ℝ (ScrewSpace k))) ℝ}
    (hM'eq :
      ((PanelHingeFramework.ofNormals G ends q).toBodyHinge.rigidityMatrixEdgeAug ends hgp rRow
          * (LinearMap.toMatrix' (prodColumnOpEquiv (k := k) (α := α)
              (BodyHingeFramework.columnOp (k := k)
                (cd.castSucc_ne_succ i)).symm).toLinearMap).transpose).submatrix
        re (columnSplit (k := k) (cd.vtx i.castSucc)).symm
        = Matrix.fromBlocks A B C D)
    (hB : B = L₀ * D)
    (hA : LinearIndependent ℝ (A - L₀ * C).row)
    (hD : LinearIndependent ℝ D.row)
    (hdef : G.deficiency n = 0) :
    PanelHingeFramework.HasGenericFullRankRealization k n G := by
  classical
  -- The split body `v := vtx i.castSucc` and its successor neighbour `a := vtx i.succ`; the
  -- distinctness `hva` and the deleted-vertex graph's cardinality facts. We do **not** `set`-fold:
  -- the final call passes the literal `cd`-forms and the carried `re`/`hM'eq`/`hr` pin `v`/`a`.
  have hva : cd.vtx i.castSucc ≠ cd.vtx i.succ := cd.castSucc_ne_succ i
  have hvG : cd.vtx i.castSucc ∈ V(G) := cd.vtx_mem _
  -- `a = vtx i.succ ≠ v` survives the deletion, so `V(G − v)` is nonempty.
  have haVc : cd.vtx i.succ ∈ V(G.removeVertex (cd.vtx i.castSucc)) := by
    rw [Graph.vertexSet_removeVertex]; exact ⟨cd.vtx_mem _, hva.symm⟩
  have hVone : 1 ≤ V(G.removeVertex (cd.vtx i.castSucc)).ncard :=
    (Set.ncard_pos (Set.toFinite _)).2 ⟨_, haVc⟩
  have hVcard : V(G).ncard = V(G.removeVertex (cd.vtx i.castSucc)).ncard + 1 := by
    rw [Graph.vertexSet_removeVertex, Set.ncard_diff_singleton_of_mem hvG]
    have : 1 ≤ V(G).ncard := (Set.ncard_pos (Set.toFinite _)).2 ⟨_, hvG⟩
    omega
  exact PanelHingeFramework.case_III_arm_realization_aug_ofNormals (k := k) G
    (G.removeVertex (cd.vtx i.castSucc)) ends (q := q)
    hva hVone hVcard hgp hends hm₁ hm₂ re hre L₀ hr hM'eq hB hA hD hdef

/-- **The interior-arm corner `hA` leaf, threaded from the discriminator's matched-candidate gate**
(`lem:case-III` general-`d`, the §(4.73.2) placement-reconciliation seam; Katoh–Tanigawa 2011 §6.4.2
eqs. (6.65)–(6.67); `notes/Phase23-design.md` §(4.73.2), `notes/Phase23f.md` D-CAN-4 build order).
The `hA : LinearIndependent ℝ A.row` hypothesis of `chainData_arm_realization_zero₁₂` (item (4) of
the D-CAN-4 plan), built — modulo the genuinely-new KT-6.66 operated-corner identity `hAeq` — from
the **direct-`q`** matched-candidate gate the discriminator
(`exists_shared_redundancy_and_matched_candidate`) outputs.

**The placement threads with NO `shiftPerm` factor.** The `_zero₁₂` cert route consumes the corner
gate at the corner leaf `corner_hA_zero₁₂_of_gate`, whose precondition is the **NONZERO** gate
`ρ₀ (F.supportExtensor e_a) ≠ 0` (KT's eq. (6.65)–(6.67) member-pick), NOT the **perpendicularity**
`ρ₀ (panelSupportExtensor (qρ(a,·)) (qρ(b,·))) = 0` that the dead-arm
`case_III_arm_corner_assembly` route's `interior_hρe₀_of_widening` produces against `q ∘ shiftPerm`.
At the matched interior candidate `i` (`0 < i`), the candidate hinge `e_a = cd.edge i` has support
extensor `panelSupportExtensor (q(vtx i.succ,·)) n'` (`caseIIICandidate_supportExtensor_candidate`,
`e_c ≠ e_r` via `pred_edge_ne`), and `cd.candidateVtx i = cd.vtx i.succ` (`candidateVtx_succ_eq`),
so the discriminator's gate `ρ₀ (panelSupportExtensor (q(candidateVtx i,·)) n') ≠ 0` IS, verbatim,
`corner_hA_zero₁₂_of_gate`'s `hρe₀` — both against the same direct `q`. No relabel-`q` perp is
consumed anywhere in the `_zero₁₂` chain (`case_III_arm_realization_rowOp` →
`case_III_rank_certification_zero₁₂` take `hA`/`hD`, never an `hρe₀`). The `hgp`/`ha`/`hAeq` block
data is the dispatch's (D-CAN-4 items (2)/(3)); this leaf is solely the gate threading. -/
theorem PanelHingeFramework.chainData_arm_corner_hA_of_discriminator_gate [DecidableEq β]
    {G : Graph α β} {n : ℕ} (cd : G.ChainData n) (i : Fin cd.d) (hi : 0 < (i : ℕ))
    {q : α × Fin (k + 2) → ℝ} (ends : β → α × α)
    {n' : Fin (k + 2) → ℝ}
    -- the spine's candidate's edge-restricted general-position hypothesis:
    (hgp : ∀ e ∈ G.edgeSet,
      (PanelHingeFramework.caseIIICandidate G ends q (cd.edge i)
        (cd.edge ⟨(i : ℕ) - 1, by omega⟩) (fun j => q (cd.vtx i.succ, j)) n'
        (fun j => q (cd.vtx (⟨(i : ℕ) - 1, by omega⟩ : Fin cd.d).castSucc, j)) 0).supportExtensor
          e ≠ 0)
    -- the candidate corner edge `e_a = cd.edge i` is a `G`-edge (chain link):
    (ha : cd.edge i ∈ G.edgeSet)
    -- the DISCRIMINATOR's matched-candidate gate at `candidateVtx i` (DIRECT `q`, no `shiftPerm`):
    {ρ₀ : Module.Dual ℝ (ScrewSpace k)}
    (hgate : ρ₀ (panelSupportExtensor (fun j => q (cd.candidateVtx i, j)) n') ≠ 0)
    -- the row-op block / coordinatization data `hA` is stated against (the spine's corner block):
    {m₁ : Type*}
    (coordEquiv : Module.Dual ℝ (ScrewSpace k) ≃ₗ[ℝ]
      ((α × Fin (Module.finrank ℝ (ScrewSpace k))) → ℝ))
    (em₁ : m₁ ≃ (Fin (screwDim k - 1) ⊕ Unit))
    {A : Matrix m₁ (α × Fin (Module.finrank ℝ (ScrewSpace k))) ℝ}
    -- the genuinely-new KT-6.66 operated-corner identity (the dispatch's D-CAN-4 obligation):
    (hAeq : A = Matrix.of (fun row => coordEquiv (Sum.elim
        (fun j : Fin (screwDim k - 1) =>
          ((PanelHingeFramework.caseIIICandidate G ends q (cd.edge i)
            (cd.edge ⟨(i : ℕ) - 1, by omega⟩) (fun j => q (cd.vtx i.succ, j)) n'
            (fun j => q (cd.vtx (⟨(i : ℕ) - 1, by omega⟩ : Fin cd.d).castSucc, j)) 0).blockBasisOn
              hgp ha j : Module.Dual ℝ (ScrewSpace k)))
        (fun _ : Unit => ρ₀) (em₁ row)))) :
    LinearIndependent ℝ A.row := by
  set F := PanelHingeFramework.caseIIICandidate G ends q (cd.edge i)
        (cd.edge ⟨(i : ℕ) - 1, by omega⟩) (fun j => q (cd.vtx i.succ, j)) n'
        (fun j => q (cd.vtx (⟨(i : ℕ) - 1, by omega⟩ : Fin cd.d).castSucc, j)) 0 with hF
  -- The candidate-hinge support extensor at `e_a = cd.edge i` is the panel meet
  -- `panelSupportExtensor (q(vtx i.succ,·)) n'` (`e_c ≠ e_r` via `pred_edge_ne`).
  have heab : cd.edge i ≠ cd.edge ⟨(i : ℕ) - 1, by omega⟩ := (cd.pred_edge_ne hi).symm
  have hsupp_ea : F.supportExtensor (cd.edge i)
      = panelSupportExtensor (fun j => q (cd.vtx i.succ, j)) n' := by
    rw [hF]
    exact PanelHingeFramework.caseIIICandidate_supportExtensor_candidate G ends q
      (fun j => q (cd.vtx i.succ, j)) n'
      (fun j => q (cd.vtx (⟨(i : ℕ) - 1, by omega⟩ : Fin cd.d).castSucc, j)) 0 heab
  -- The discriminator's gate vertex `candidateVtx i = vtx i.succ` (interior, `0 < i`).
  have hcv : cd.candidateVtx i = cd.vtx i.succ := cd.candidateVtx_succ_eq hi
  -- Thread the discriminator NONZERO gate into the candidate-slot gate `hρe₀`.
  have hρe₀ : ρ₀ (F.supportExtensor (cd.edge i)) ≠ 0 := by
    rw [hsupp_ea, ← hcv]; exact hgate
  -- Fire `corner_hA_zero₁₂_of_gate` — the NONZERO gate, NOT the perp.
  exact F.corner_hA_zero₁₂_of_gate hgp ha hρe₀ coordEquiv em₁ hAeq

/-- **The genuine-`ofNormals` interior-arm corner `hA` leaf, threaded from the chain-edge gate**
(`lem:case-III` general-`d`, the (D-substitution) corner-`hA` leaf for the genuine geometry arm;
Katoh–Tanigawa 2011 §6.4.2 eqs.~(6.59)/(6.66); `notes/Phase23-design.md` §(4.88.1) [the
arm-hypothesis ↔ source map, the operated `corner_hA_zero₁₂_of_gate` corner-`hA` slot],
`notes/Phase23f.md` Gap B [the `cd`-taking `_ofNormals` spine]). The `_ofNormals` sibling of
`chainData_arm_corner_hA_of_discriminator_gate`: the operated corner-`hA`
(`LinearIndependent ℝ A.row`) the GENUINE-framework arm `case_III_arm_realization_aug_ofNormals`
(`ForkedArm.lean:1309`) takes as block data, threaded from the chain-edge-panel gate at the genuine
panel-hinge framework `F = ofNormals G ends q` (KT 6.59, `v = vtx i.castSucc` re-inserted at its
genuine seed), with NO `caseIIICandidate` extensor override.

**The genuine framing CLEANS the §(4.73.2) seam the override hit.** Under (D-substitution) the
corner edge `e_a = cd.edge i` is the literal chain edge recording `ends e_a = (v, a) =
(vtx i.castSucc, vtx i.succ)`, so its support extensor is the GENUINE chain-edge panel
`F.supportExtensor e_a = panelSupportExtensor (q(v,·)) (q(a,·))`
(`ofNormals_supportExtensor_eq_panel_of_ends`, a pure unfold of `toBodyHinge_supportExtensor` /
`ofNormals_{normal,ends}`) — NOT the override `panelSupportExtensor (q(a,·)) n'` the
`caseIIICandidate` accessor read. So the gate is at the chain-edge panel `(v, a)` itself, the SAME
panel the LANDED chain-edge perp `baseRedundancy_perp_interior_reproduced_panel` reads for the `hr`
membership (S1 leaf), and the false short-circuit panel `(vtx (i+1), vtx (i−1))` that killed the
six narrow routes (design §§(4.77)–(4.83)) never appears.

The operated corner is closed by the LANDED `corner_hA_zero₁₂_of_gate` (`Concrete.lean`): the
genuinely-new KT-6.66 operated-corner identity `hAeq` (the operated block reads the `D`-member
family `[blockBasisOn(e_a, ·); ρ₀]`, reindexed across `m₁` by `em₁`) reduces the row-LI to the gate
`ρ₀ (F.supportExtensor e_a) ≠ 0`, threaded here from `hgate` (the chain-edge-panel form) via the
genuine support read. The `hgp`/`ha`/`coordEquiv`/`em₁`/`hAeq` block data is the dispatch's (the
genuine `_aug` block-data assembly, design §(4.79.5) 5f); this leaf is solely the gate threading.
No `\lean` pin (internal infra; the chain dispatch carries the blueprint node). -/
theorem PanelHingeFramework.chainData_arm_corner_hA_ofNormals_of_gate
    {G : Graph α β} {n : ℕ} (cd : G.ChainData n) (i : Fin cd.d)
    {q : α × Fin (k + 2) → ℝ} (ends : β → α × α)
    -- the genuine framework's edge-restricted general-position hypothesis:
    (hgp : ∀ e ∈ (PanelHingeFramework.ofNormals G ends q).toBodyHinge.graph.edgeSet,
      (PanelHingeFramework.ofNormals G ends q).toBodyHinge.supportExtensor e ≠ 0)
    -- the corner chain edge `e_a = cd.edge i` is a `G`-edge (= an edge of the genuine framework):
    (ha : cd.edge i ∈ (PanelHingeFramework.ofNormals G ends q).toBodyHinge.graph.edgeSet)
    -- the GENUINE `ends`-recording at the chain edge: `e_a ↦ (v, a) =
    -- (vtx i.castSucc, vtx i.succ)`:
    (hends_ea : ends (cd.edge i) = (cd.vtx i.castSucc, cd.vtx i.succ))
    -- the chain-edge-panel gate (the genuine analogue of the discriminator's matched gate; at the
    -- chain-edge panel `(v, a)`, the SAME panel the S1 `hr` membership reads):
    {ρ₀ : Module.Dual ℝ (ScrewSpace k)}
    (hgate : ρ₀ (panelSupportExtensor (fun j => q (cd.vtx i.castSucc, j))
        (fun j => q (cd.vtx i.succ, j))) ≠ 0)
    -- the row-op block / coordinatization data `hA` is stated against (the spine's corner block):
    {m₁ κ : Type*}
    (coordEquiv : Module.Dual ℝ (ScrewSpace k) ≃ₗ[ℝ] (κ → ℝ))
    (em₁ : m₁ ≃ (Fin (screwDim k - 1) ⊕ Unit))
    {A : Matrix m₁ κ ℝ}
    -- the genuinely-new KT-6.66 operated-corner identity (the dispatch's block-data obligation):
    (hAeq : A = Matrix.of (fun i' => coordEquiv (Sum.elim
        (fun j : Fin (screwDim k - 1) =>
          ((PanelHingeFramework.ofNormals G ends q).toBodyHinge.blockBasisOn hgp ha j
            : Module.Dual ℝ (ScrewSpace k)))
        (fun _ : Unit => ρ₀) (em₁ i')))) :
    LinearIndependent ℝ A.row := by
  set F := (PanelHingeFramework.ofNormals G ends q).toBodyHinge with hF
  -- The genuine chain-edge support extensor is the literal chain-edge panel
  -- `panelSupportExtensor (q(v,·)) (q(a,·))` (`ofNormals_supportExtensor_eq_panel_of_ends`).
  have hsupp_ea : F.supportExtensor (cd.edge i)
      = panelSupportExtensor (fun j => q (cd.vtx i.castSucc, j))
        (fun j => q (cd.vtx i.succ, j)) := by
    rw [hF]
    exact PanelHingeFramework.ofNormals_supportExtensor_eq_panel_of_ends G (cd.edge i) hends_ea
  -- Thread the chain-edge-panel gate into the candidate-slot gate `hρe₀`.
  have hρe₀ : ρ₀ (F.supportExtensor (cd.edge i)) ≠ 0 := by rw [hsupp_ea]; exact hgate
  -- Fire `corner_hA_zero₁₂_of_gate` — the NONZERO gate at the genuine chain-edge panel.
  exact F.corner_hA_zero₁₂_of_gate hgp ha hρe₀ coordEquiv em₁ hAeq

/-- **The interior-arm corner block-basis family is row-LI from the 3-normal LI** (Phase 23f, the
`ρ₀`-free corner-LI core specialized to the spine candidate binding; Katoh–Tanigawa 2011 §6.4.2 eqs.
(6.64)–(6.66), the `Mᵢ`-block full-rank input; `notes/Phase23-design.md` §(4.75.3) route (a)). The
escape half of the pin-zero corner `hA`: under the pin-zero (literal-IH-`Gab`) bottom the operated
corner `A − L₀·C = A` reads the un-operated `blockBasisOn` family
`[blockBasisOn(e_a, ·); blockBasisOn(e_b, j₀)]` (`linearIndependent_toBlocks₁₁_row_of_corner_gate`,
the `C = 0` collapse via `rigidityMatrixEdge_mul_columnOp_submatrix_toBlocks₂₁_eq_zero`), whose
row-LI needs only **block incomparability** `¬ hingeRowBlock e_b ≤ hingeRowBlock e_a`. This leaf
supplies that family LI from the genuinely-new **direct-`q` 3-normal LI** `![q a, n', q b]` (with
`a = vtx i.succ` the candidate panel, `b = vtx (i−1)` the reproduced panel, `n'` the discriminator
transversal), threading the spine's exact candidate binding:

* the candidate-slot support `C(e_a) = panelSupportExtensor (q a) n'`
  (`caseIIICandidate_supportExtensor_candidate`, `e_c ≠ e_r` via `pred_edge_ne`);
* the reproduced-slot support at `t = 0` `C(e_b) = panelSupportExtensor (q a) (q b)`
  (`caseIIICandidate_supportExtensor_reproduced` + `zero_smul`/`add_zero`);
* the non-parallelism `C(e_a) ∉ span {C(e_b)}` from the 3-normal LI
  (`panelSupportExtensor_not_mem_span_of_triLI`, the panel-meet leaf);
* incomparability (`hingeRowBlock_not_le_of_supportExtensor_not_mem_span`) → the corner family LI
  (`exists_corner_blockBasisOn_linearIndependent_of_not_le`).

The 3-normal LI is **direct-`q`**: the spine `chainData_arm_realization_zero₁₂` places the candidate
against the direct seed `q` (forced by the discriminator's direct-`q` NONZERO gate
`ρ₀ (panelSupportExtensor (q(candidateVtx i)) n') ≠ 0` the corner `hA` consumes, NOT the relabel-`q`
`q ∘ shiftPerm`). So the corner's reproduced panel is the direct-`q` short-circuit panel
`(vtx (i+1), vtx (i−1))` — distinct from the chain-edge panel `(vtx (i+1), vtx i)` the landed perp
crux `baseRedundancy_perp_interior_reproduced_panel` produces (that is the relabel-`q`-equivalent
panel; the §(4.73.2) seam is REAL for the perp gate). Hence route (a) — the 3-normal LI — rather
than route (b)'s direct-`q` perp; the 3-normal LI `![q a, n', q b]` is the carried genuinely-new
input (`n'` off `span {q a, q b}`, KT general position on the panels — not a discriminator output).
NO `ScrewSpace` unfolding. -/
theorem PanelHingeFramework.chainData_arm_corner_blockBasis_linearIndependent_of_triLI
    [DecidableEq β] {G : Graph α β} {n : ℕ} (cd : G.ChainData n) (i : Fin cd.d) (hi : 0 < (i : ℕ))
    {q : α × Fin (k + 2) → ℝ} (ends : β → α × α) {n' : Fin (k + 2) → ℝ}
    (hgp : ∀ e ∈ (PanelHingeFramework.caseIIICandidate G ends q (cd.edge i)
      (cd.edge ⟨(i : ℕ) - 1, by omega⟩) (fun j => q (cd.vtx i.succ, j)) n'
      (fun j => q (cd.vtx (⟨(i : ℕ) - 1, by omega⟩ : Fin cd.d).castSucc, j)) 0).graph.edgeSet,
      (PanelHingeFramework.caseIIICandidate G ends q (cd.edge i)
      (cd.edge ⟨(i : ℕ) - 1, by omega⟩) (fun j => q (cd.vtx i.succ, j)) n'
      (fun j => q (cd.vtx (⟨(i : ℕ) - 1, by omega⟩ : Fin cd.d).castSucc, j)) 0).supportExtensor
        e ≠ 0)
    (ha : cd.edge i ∈ G.edgeSet) (hb : cd.edge ⟨(i : ℕ) - 1, by omega⟩ ∈ G.edgeSet)
    -- the genuinely-new SOURCE: the direct-`q` 3-normal LI `![q a, n', q b]`:
    (htriLI : LinearIndependent ℝ
      (![(fun j => q (cd.vtx i.succ, j)), n',
         (fun j => q (cd.vtx (⟨(i : ℕ) - 1, by omega⟩ : Fin cd.d).castSucc, j))]
       : Fin 3 → Fin (k + 2) → ℝ)) :
    ∃ j₀ : Fin (screwDim k - 1), LinearIndependent ℝ (Sum.elim
      (fun j : Fin (screwDim k - 1) =>
        ((PanelHingeFramework.caseIIICandidate G ends q (cd.edge i)
          (cd.edge ⟨(i : ℕ) - 1, by omega⟩) (fun j => q (cd.vtx i.succ, j)) n'
          (fun j => q (cd.vtx (⟨(i : ℕ) - 1, by omega⟩ : Fin cd.d).castSucc, j)) 0).blockBasisOn
            hgp ha j : Module.Dual ℝ (ScrewSpace k)))
      (fun _ : Unit => ((PanelHingeFramework.caseIIICandidate G ends q (cd.edge i)
          (cd.edge ⟨(i : ℕ) - 1, by omega⟩) (fun j => q (cd.vtx i.succ, j)) n'
          (fun j => q (cd.vtx (⟨(i : ℕ) - 1, by omega⟩ : Fin cd.d).castSucc, j)) 0).blockBasisOn
            hgp hb j₀ : Module.Dual ℝ (ScrewSpace k)))) := by
  set F := PanelHingeFramework.caseIIICandidate G ends q (cd.edge i)
      (cd.edge ⟨(i : ℕ) - 1, by omega⟩) (fun j => q (cd.vtx i.succ, j)) n'
      (fun j => q (cd.vtx (⟨(i : ℕ) - 1, by omega⟩ : Fin cd.d).castSucc, j)) 0 with hF
  -- The candidate-slot support `C(e_a) = panelSupportExtensor (q a) n'`.
  have hsupp_ea : F.supportExtensor (cd.edge i)
      = panelSupportExtensor (fun j => q (cd.vtx i.succ, j)) n' := by
    rw [hF]
    exact PanelHingeFramework.caseIIICandidate_supportExtensor_candidate G ends q _ n' _ 0
      (cd.pred_edge_ne hi).symm
  -- The reproduced-slot support at `t = 0` `C(e_b) = panelSupportExtensor (q a) (q b)`.
  have hsupp_eb : F.supportExtensor (cd.edge ⟨(i : ℕ) - 1, by omega⟩)
      = panelSupportExtensor (fun j => q (cd.vtx i.succ, j))
          (fun j => q (cd.vtx (⟨(i : ℕ) - 1, by omega⟩ : Fin cd.d).castSucc, j)) := by
    rw [hF, PanelHingeFramework.caseIIICandidate_supportExtensor_reproduced, zero_smul, add_zero]
  -- Non-parallelism from the 3-normal LI, then incomparability → corner family LI.
  have hpar : F.supportExtensor (cd.edge i) ∉
      Submodule.span ℝ {F.supportExtensor (cd.edge ⟨(i : ℕ) - 1, by omega⟩)} := by
    rw [hsupp_ea, hsupp_eb]
    exact panelSupportExtensor_not_mem_span_of_triLI _ _ _ htriLI
  exact F.exists_corner_blockBasisOn_linearIndependent_of_not_le hgp ha hb
    (F.hingeRowBlock_not_le_of_supportExtensor_not_mem_span hpar)

/-- **CHAIN-2c-i — the single-discriminator pick off the shared `ρ₀`** (`lem:case-III` general-`d`;
Katoh–Tanigawa 2011 §6.4.2, Lemma 6.13 eqs. (6.67), the `d`-panel discriminator; Phase 23b). The
`Fin (k+1)`-family form of the `d = 3` dispatch's discriminator region
(`case_III_candidate_dispatch` step 5, `Realization.lean:435`–442). From an
algebraically-independent base normal family `q`, a `Fin (k+1)`-tuple `cand` of **distinct**
candidate vertices (KT's panels `Πᵢ`, one per chain candidate — `Π₀ = Π(v₀)`, `Πᵢ = Π(vᵢ₊₁)`),
and the **single** redundancy functional `ρ` of the `v₁`-split (`ρ ≠ 0`, the shared `r` produced
once by `chainData_split_w6b_gates`), it picks a discriminating panel index `u : Fin (k+1)` and a
transversal normal `n'` of `Π(cand u)` such that `ρ` does *not* annihilate the candidate
`cand u`-hinge's supporting extensor `panelSupportExtensor (q(cand u, ·)) n'`.

This is **steps 1–3 of the single-base chain dispatch** (`notes/Phase23-design.md` §(n), route β —
the W6b call producing `ρ` is the already-landed `chainData_split_w6b_gates`; here is the panel-LI
+ the *one* discriminator call). It is the faithful `Fin (k+1)`-generalization of the green `d = 3`
discriminator and is **independent of the relabel-arm crux** (the uniform `Fin (k+1)` `u`↔candidate
match, CHAIN-2c-ii): the panel index `u` it returns is arbitrary; matching it to a chain candidate
and transporting `ρ` to that candidate's role is the deferred step 4.

Mechanism (the eqs. (6.65)–(6.67) one shot, no separate ±r-chain lemma — KT eq. (6.66) is absorbed
into reusing the single `ρ` here, §(n) clause (i)):
* The `k+1` panel normals `fun i j => q (cand i, j)` are `ℝ`-linearly independent — the OD-7 LEAF-0
  `linearIndependent_normals_of_algebraicIndependent_general` at the injective selector `cand`.
* `exists_homogeneousIncidence_of_normals_gen` exhibits the `k+2` homogeneous witness points `pbar`
  (LI; `pbar 0` on every panel, `pbar i.succ` off panel `n i` only) — KT eq. (6.45)'s incidence
  pattern, the OD-4 homogeneous route (no affine independence).
* `exists_complementIso_ne_zero_of_homogeneousIncidence_gen` (CHAIN-4d, the Claim-6.12 capstone)
  with `r := ρ` returns the discriminating `(u, n')` and the meet-form non-annihilation
  `ρ(complementIso ⟨extensor ![n u, n'], _⟩) ≠ 0`; the bridge
  `panelSupportExtensor_eq_complementIso_extensor` rewrites it into the `panelSupportExtensor` form
  the per-`i` arm closer (`htrans` slot of `chainData_split_realization`) consumes.

Graph-free over `ScrewSpace k` (no `d = 3` content; the discriminator is already general-`k`); no
motive/IH change. No `\lean` pin (internal infra; the chain dispatch carries the blueprint node). -/
theorem PanelHingeFramework.exists_chainData_discriminator_pick {k : ℕ}
    {α : Type*} {q : α × Fin (k + 2) → ℝ} (hq : AlgebraicIndependent ℚ q)
    {cand : Fin (k + 1) → α} (hcand : Function.Injective cand)
    {ρ : Module.Dual ℝ (ScrewSpace k)} (hρ : ρ ≠ 0) :
    ∃ (u : Fin (k + 1)) (n' : Fin (k + 2) → ℝ),
      LinearIndependent ℝ ![fun j => q (cand u, j), n'] ∧
      ρ (panelSupportExtensor (fun j => q (cand u, j)) n') ≠ 0 := by
  -- The `k+1` panel normals are linearly independent (OD-7 LEAF-0 at the injective `cand`).
  have hn : LinearIndependent ℝ (fun (i : Fin (k + 1)) (j : Fin (k + 2)) => q (cand i, j)) :=
    linearIndependent_normals_of_algebraicIndependent_general hq hcand
  -- The `k+2` homogeneous witness points (KT eq. (6.45) incidence; the OD-4 homogeneous route).
  obtain ⟨pbar, hp, h0, hi⟩ := exists_homogeneousIncidence_of_normals_gen hn
  -- The Claim-6.12 discriminator (CHAIN-4d): the discriminating `(u, n')` and meet-form gate.
  obtain ⟨u, n', hpair, hgate⟩ :=
    BodyHingeFramework.exists_complementIso_ne_zero_of_homogeneousIncidence_gen hρ hp hn h0
      (fun i j hji => (hi i).1 j hji)
  -- Bridge the meet form into the `panelSupportExtensor` form the arm closer consumes.
  exact ⟨u, n', hpair, by rwa [panelSupportExtensor_eq_complementIso_extensor]⟩

/-- **CHAIN-2c-iii LEAF-3 — fire the shared redundancy + panel discriminator off the base split**
(`lem:case-III` general-`d`; Katoh–Tanigawa 2011 §6.4.2, Lemma 6.13 eqs. (6.65)–(6.67); Phase 23c).
The discriminator-firing producer the general-`d` dispatch (`chainData_dispatch`) calls ONCE at the
**base `v₁`-split** to pin the **single** shared redundancy functional `ρ₀` and the **matched**
chain candidate `i` whose panel the Claim-6.12 discriminator selects.

From the base split `(v, a, b)` of the chain (the body `v`, its two chain neighbours `a`, `b`, and
the fresh short-circuit `e₀`), with the eq.-(6.22) nested-IH rank bound `h622lb` and the IH-generic
base realization `hsplitGP`, this:
* fires `chainData_split_w6b_gates` ONCE → the candidate functional `ρ₀ ≠ 0` (the eqs.
  (6.23)/(6.52) redundancy of the `(ab)`-row), its base panel annihilation `ρ₀(C(ab)) = 0`, the
  `screwDim k · (|V(Gab)| − 1)` independent bottom rows `w` (each a `Gᵥ`-row or a candidate-hinge),
  the eq.-(6.52) `λ`-grouped `(ab)`-witness `ρ₀ = Σⱼ λⱼ (rab j)`, the **edge-grouped `G_v`-row
  widening** of `hingeRow a b ρ₀` (KT eq. (6.66); re-exposed — previously discarded — so the
  interior arm can feed it to `Graph.ChainData.interior_hρe₀_of_widening`), and the seed's algebraic
  independence `AlgebraicIndependent ℚ q` — the **base bundle** LEAF-4 threads into the corner;
* fires `exists_chainData_discriminator_pick` ONCE off the base seed `q` and that **same** `ρ₀`,
  fed the `Fin (k+1)` panel selector `cd.candidatePanel hn`
  (`= candidateVtx ∘ Fin.cast d_eq_kAdd.symm`, injective) → a discriminating panel index `u`, a
  transversal `n'`, and the gate `ρ₀(panelSupportExtensor (q(candidateVtx i,·)) n') ≠ 0` at the
  **matched candidate** `i := Fin.cast (cd.d_eq_kAdd hn).symm u : Fin cd.d` (the panel→candidate
  transport across `cd.d = k + 1`, `candidatePanel_apply`).

The matched candidate `i` is **arbitrary** (the discriminator may pick the base panel `Π(v₀)` at
`u = 0` or any interior panel `Πᵢ` at `u ≠ 0`); the dispatch router (CHAIN-2c-iii LEAF-5)
case-splits on `(i : ℕ)` — base/`d=3`-floor via `chainData_split_realization`, interior `0 < i` via
the chain arm `case_III_arm_corner_assembly`. This LEAF does **not** produce the interior `hρe₀`
(KT eq. (6.66), the genuinely-new redundancy-carry leaf
`baseRedundancy_perp_interior_reproduced_panel`): that is LEAF-4 / `interior_hρe₀_of_widening`, fed
this LEAF's base `ρ₀`/`λ`-witness bundle **and the now-exposed edge-grouped `G_v`-row widening**
(`notes/Phase23-design.md` §I.8.24(4.12)). No `d = 3` content; no motive/IH change (the cert is
`hρGv`-free and `ρ₀`-agnostic, the matched-candidate machinery sits below the frozen contract). -/
theorem PanelHingeFramework.exists_shared_redundancy_and_matched_candidate
    [Finite α] [Finite β]
    {G : Graph α β} {n : ℕ} (cd : G.ChainData n) (hk1 : 1 ≤ k)
    (hn : Graph.bodyBarDim n = screwDim k)
    (v a b : α) (hav : a ≠ v) (hbv : b ≠ v) (hba : b ≠ a)
    (haG : a ∈ V(G)) (hbG : b ∈ V(G)) (he₀ : cd.e₀ ∉ E(G))
    (h622lb : ∀ (ends : β → α × α) (q : α × Fin (k + 2) → ℝ),
      (∀ e u w, (G.splitOff v a b cd.e₀).IsLink e u w → ends e = (u, w) ∨ ends e = (w, u)) →
      (∀ x y : α, x ≠ y → LinearIndependent ℝ ![fun i => q (x, i), fun i => q (y, i)]) →
      AlgebraicIndependent ℚ q →
      screwDim k * (V(G.splitOff v a b cd.e₀).ncard - 1) - (screwDim k - 2)
        ≤ Module.finrank ℝ (Submodule.span ℝ
            (PanelHingeFramework.ofNormals (G.removeVertex v) ends
              q).toBodyHinge.rigidityRows))
    (hdef_Gab : (G.splitOff v a b cd.e₀).deficiency n = 0)
    (hsplitGP : PanelHingeFramework.HasGenericFullRankRealization k n (G.splitOff v a b cd.e₀)) :
    ∃ (q : α × Fin (k + 2) → ℝ) (ends : β → α × α)
      (ρ₀ : Module.Dual ℝ (ScrewSpace k))
      (w : Fin (screwDim k * (V(G.splitOff v a b cd.e₀).ncard - 1)) →
        Module.Dual ℝ (α → ScrewSpace k))
      (lamAB : Fin (screwDim k - 1) → ℝ)
      (rab : Fin (screwDim k - 1) → Module.Dual ℝ (ScrewSpace k))
      (i : Fin cd.d) (n' : Fin (k + 2) → ℝ),
      -- the base framework data, for LEAF-4's other gates and the corner-block relabel image
      (PanelHingeFramework.ofNormals (G.splitOff v a b cd.e₀) ends q).IsGeneralPosition ∧
      (∀ e u w, (G.removeVertex v).IsLink e u w →
        (G.removeVertex v).IsLink e (ends e).1 (ends e).2) ∧
      AlgebraicIndependent ℚ q ∧
      -- the shared redundancy `ρ₀` (the single functional the cert reads everywhere)
      ρ₀ ≠ 0 ∧
      ρ₀ (panelSupportExtensor (fun j => q (a, j)) (fun j => q (b, j))) = 0 ∧
      -- the base W6b bottom family + the eq.-(6.52) `λ`-grouped `(ab)`-witness (LEAF-4's block `W`)
      LinearIndependent ℝ w ∧
      (∀ j, w j ∈
          (PanelHingeFramework.ofNormals (G.removeVertex v) ends q).toBodyHinge.rigidityRows ∨
        ∃ ρ' : Module.Dual ℝ (ScrewSpace k),
          ρ' (panelSupportExtensor (fun j => q (a, j)) (fun j => q (b, j))) = 0 ∧
          w j = BodyHingeFramework.hingeRow a b ρ') ∧
      (∀ j, rab j ∈ BodyHingeFramework.hingeRowBlock
        (PanelHingeFramework.ofNormals (G.splitOff v a b cd.e₀) ends q).toBodyHinge cd.e₀) ∧
      ρ₀ = ∑ j, lamAB j • rab j ∧
      -- the **edge-grouped** `G_v`-row widening of the shared redundancy `hingeRow a b ρ₀` (KT
      -- eq. (6.66); the bundle `chainData_split_w6b_gates` computes but LEAF-3 previously
      -- discarded), re-exposed for the interior arm's `hρe₀` leaf
      -- `Graph.ChainData.interior_hρe₀_of_widening`.
      (∃ (nGv : ℕ) (cGv : Fin nGv → ℝ) (evGv : Fin nGv → β) (uvGv vvGv : Fin nGv → α)
          (rvGv : Fin nGv → Module.Dual ℝ (ScrewSpace k)),
        (∀ j, (G.removeVertex v).IsLink (evGv j) (uvGv j) (vvGv j)) ∧
        (∀ j, rvGv j ∈ ((PanelHingeFramework.ofNormals (G.removeVertex v) ends q).toBodyHinge
          ).hingeRowBlock (evGv j)) ∧
        BodyHingeFramework.hingeRow a b ρ₀
          = ∑ j, cGv j • BodyHingeFramework.hingeRow (uvGv j) (vvGv j) (rvGv j)) ∧
      -- the matched-candidate discriminator gate at `candidateVtx i` (panel→candidate via `d=k+1`)
      LinearIndependent ℝ ![fun j => q (cd.candidateVtx i, j), n'] ∧
      ρ₀ (panelSupportExtensor (fun j => q (cd.candidateVtx i, j)) n') ≠ 0 ∧
      -- §(4.100) (B′), re-exposed for the interior-arm `hρGv` leaf re-target (both already
      -- computed by `chainData_split_w6b_gates`, previously dropped here):
      -- (1) the **genuine base redundancy span** `hingeRow a b ρ₀ ∈ span R(Gᵥ = G − v)` at the
      --     honest base selector `ends` (`_hρ₀Gv`, the input to the re-targeted leaf's `hφ₀`):
      BodyHingeFramework.hingeRow a b ρ₀ ∈ Submodule.span ℝ
        (PanelHingeFramework.ofNormals (G.removeVertex v) ends q).toBodyHinge.rigidityRows ∧
      -- (2) the **full `Gab`-link recording disjunction** (incl. `e₀`): `ends` records every
      --     `Gab = G.splitOff v a b e₀` link as `(u,w)` or `(w,u)` (the `hrec'` conjunct):
      (∀ e u w, (G.splitOff v a b cd.e₀).IsLink e u w → ends e = (u, w) ∨ ends e = (w, u)) := by
  -- W6b once at the base split: the shared `ρ₀`, the bottom family, the `λ`-witness, alg-indep `q`.
  obtain ⟨q, ends, ρ₀, w, lamAB, rab, hgp, hends', hρ₀ne, hρ₀e₀, hρ₀Gv, hw,
      hwmem, hrab_blk, hρ₀_lam, hedgeGv, hQalg, hrecGab⟩ :=
    PanelHingeFramework.chainData_split_w6b_gates hk1 G v a b cd.e₀ hav hbv hba haG hbG
      he₀ h622lb hdef_Gab hsplitGP
  -- The discriminator once off the same base seed `q` and shared `ρ₀`, fed the `Fin (k+1)` panel
  -- selector `candidatePanel hn` (injective via `candidatePanel_injective hn`).
  obtain ⟨u, n', hLI, hgate⟩ :=
    PanelHingeFramework.exists_chainData_discriminator_pick hQalg
      (cd.candidatePanel_injective hn) hρ₀ne
  -- The matched candidate `i := Fin.cast d_eq_kAdd.symm u`; rewrite `candidatePanel hn u` to
  -- `candidateVtx i` (the `rfl`-level `candidatePanel_apply` bridge). §(4.100) (B′): the base
  -- redundancy span `hρ₀Gv` + the full `Gab`-link recording `hrecGab` are now re-exposed.
  refine ⟨q, ends, ρ₀, w, lamAB, rab, Fin.cast (cd.d_eq_kAdd hn).symm u, n', hgp, hends', hQalg,
    hρ₀ne, hρ₀e₀, hw, hwmem, hrab_blk, hρ₀_lam, hedgeGv, ?_, ?_, hρ₀Gv, hrecGab⟩
  · rw [← cd.candidatePanel_apply hn u]; exact hLI
  · rw [← cd.candidatePanel_apply hn u]; exact hgate

/-- **CHAIN-2c-iii LEAF-5 — fire the base-split discriminator off a `ChainData`** (`lem:case-III`
general-`d`; Katoh–Tanigawa 2011 §6.4.2, Lemma 6.13 eqs. (6.65)–(6.67); Phase 23f). The
`ChainData`-shaped firing producer the chain dispatch (`chainData_dispatch`) calls ONCE at the
**base `v₁`-split** `(v, a, b) = (vtx 1, vtx 0, vtx 2)`: it derives the eq.-(6.22) nested-IH rank
bound `h622lb` from `case_III_nested_rank_lower_all_k` (the base body `vtx 1` is the degree-2 chain
vertex, its two `G`-edges the chain edges `edge 0 : vtx 0—vtx 1` / `edge 1 : vtx 1—vtx 2`), then
calls `exists_shared_redundancy_and_matched_candidate` to pin the shared redundancy `ρ₀` and the
matched chain candidate `i`.

This removes the router's manual `h622lb` derivation + base-split-tuple bookkeeping: it consumes a
`ChainData cd` (with `2 ≤ cd.d`, from `cd.d = k + 1` and `1 ≤ k`, so `vtx 2` exists), the all-`k`
IH (the `chainData_split_realization` / `case_III_realization_all_k` shape), `hdef`/`hdef_Gab`, and
the IH-generic base realization `hsplitGP`, and produces the discriminator's full output bundle
**already stated at the base split `(vtx 1, vtx 0, vtx 2)`** — exactly the verbatim input shape
`chainData_dispatch_interior_of_discriminator` (the interior arm) and the floor route
(`chainData_split_realization` at chain index 1, the same base split up to the `a/b`-swap) consume.

The matched candidate `i` is **arbitrary** (the discriminator may pick the head panel `Π(v₀)` at
`i = 0`, the base neighbour `Π(v₂)` at `i = 1`, or any interior panel `Πᵢ` at `2 ≤ i`); the router
case-splits `(i : ℕ)` and routes. No `d = 3` content; no motive/IH change (the firing is below the
frozen contract). No `\lean` pin (internal infra; the chain dispatch carries the blueprint node). -/
theorem PanelHingeFramework.chainData_fire_discriminator
    [DecidableEq β] [Finite α] [Finite β]
    {G : Graph α β} {n : ℕ} (cd : G.ChainData n) (hd2 : 2 ≤ cd.d) (hk1 : 1 ≤ k)
    (hn : Graph.bodyBarDim n = screwDim k)
    (hG : G.IsMinimalKDof n 0) (hV3 : 3 ≤ V(G).ncard) (hSimple : G.Simple)
    (hIH : ∀ (k' : ℤ) (G' : Graph α β), G'.IsMinimalKDof n k' → V(G').Nonempty →
      V(G').ncard < V(G).ncard →
      (G'.Simple → PanelHingeFramework.HasGenericFullRankRealization k n G') ∧
        HasPanelRealization k n G')
    (hdef_Gab : (G.splitOff (cd.vtx ⟨1, by omega⟩) (cd.vtx ⟨0, by omega⟩)
      (cd.vtx ⟨2, by omega⟩) cd.e₀).deficiency n = 0)
    (hsplitGP : PanelHingeFramework.HasGenericFullRankRealization k n
      (G.splitOff (cd.vtx ⟨1, by omega⟩) (cd.vtx ⟨0, by omega⟩) (cd.vtx ⟨2, by omega⟩) cd.e₀)) :
    ∃ (q : α × Fin (k + 2) → ℝ) (ends : β → α × α)
      (ρ₀ : Module.Dual ℝ (ScrewSpace k))
      (w : Fin (screwDim k * (V(G.splitOff (cd.vtx ⟨1, by omega⟩) (cd.vtx ⟨0, by omega⟩)
          (cd.vtx ⟨2, by omega⟩) cd.e₀).ncard - 1)) → Module.Dual ℝ (α → ScrewSpace k))
      (lamAB : Fin (screwDim k - 1) → ℝ)
      (rab : Fin (screwDim k - 1) → Module.Dual ℝ (ScrewSpace k))
      (i : Fin cd.d) (n' : Fin (k + 2) → ℝ),
      (PanelHingeFramework.ofNormals (G.splitOff (cd.vtx ⟨1, by omega⟩) (cd.vtx ⟨0, by omega⟩)
        (cd.vtx ⟨2, by omega⟩) cd.e₀) ends q).IsGeneralPosition ∧
      (∀ e u w, (G.removeVertex (cd.vtx ⟨1, by omega⟩)).IsLink e u w →
        (G.removeVertex (cd.vtx ⟨1, by omega⟩)).IsLink e (ends e).1 (ends e).2) ∧
      AlgebraicIndependent ℚ q ∧
      ρ₀ ≠ 0 ∧
      ρ₀ (panelSupportExtensor (fun j => q (cd.vtx ⟨0, by omega⟩, j))
        (fun j => q (cd.vtx ⟨2, by omega⟩, j))) = 0 ∧
      LinearIndependent ℝ w ∧
      (∀ j, w j ∈ (PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx ⟨1, by omega⟩))
          ends q).toBodyHinge.rigidityRows ∨
        ∃ ρ' : Module.Dual ℝ (ScrewSpace k),
          ρ' (panelSupportExtensor (fun j => q (cd.vtx ⟨0, by omega⟩, j))
            (fun j => q (cd.vtx ⟨2, by omega⟩, j))) = 0 ∧
          w j = BodyHingeFramework.hingeRow (cd.vtx ⟨0, by omega⟩) (cd.vtx ⟨2, by omega⟩) ρ') ∧
      (∀ j, rab j ∈ BodyHingeFramework.hingeRowBlock
        (PanelHingeFramework.ofNormals (G.splitOff (cd.vtx ⟨1, by omega⟩) (cd.vtx ⟨0, by omega⟩)
          (cd.vtx ⟨2, by omega⟩) cd.e₀) ends q).toBodyHinge cd.e₀) ∧
      ρ₀ = ∑ j, lamAB j • rab j ∧
      (∃ (nGv : ℕ) (cGv : Fin nGv → ℝ) (evGv : Fin nGv → β) (uvGv vvGv : Fin nGv → α)
          (rvGv : Fin nGv → Module.Dual ℝ (ScrewSpace k)),
        (∀ j, (G.removeVertex (cd.vtx ⟨1, by omega⟩)).IsLink (evGv j) (uvGv j) (vvGv j)) ∧
        (∀ j, rvGv j ∈ ((PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx ⟨1, by omega⟩))
          ends q).toBodyHinge).hingeRowBlock (evGv j)) ∧
        BodyHingeFramework.hingeRow (cd.vtx ⟨0, by omega⟩) (cd.vtx ⟨2, by omega⟩) ρ₀
          = ∑ j, cGv j • BodyHingeFramework.hingeRow (uvGv j) (vvGv j) (rvGv j)) ∧
      LinearIndependent ℝ ![fun j => q (cd.candidateVtx i, j), n'] ∧
      ρ₀ (panelSupportExtensor (fun j => q (cd.candidateVtx i, j)) n') ≠ 0 ∧
      BodyHingeFramework.hingeRow (cd.vtx ⟨0, by omega⟩) (cd.vtx ⟨2, by omega⟩) ρ₀ ∈
        Submodule.span ℝ (PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx ⟨1, by omega⟩))
          ends q).toBodyHinge.rigidityRows ∧
      (∀ e u w, (G.splitOff (cd.vtx ⟨1, by omega⟩) (cd.vtx ⟨0, by omega⟩)
        (cd.vtx ⟨2, by omega⟩) cd.e₀).IsLink e u w → ends e = (u, w) ∨ ends e = (w, u)) := by
  -- The base split tuple `(v, a, b) = (vtx 1, vtx 0, vtx 2)`, with chain edges `edge 0 : v₀—v₁`,
  -- `edge 1 : v₁—v₂` (oriented *out of* the base body `v₁`).
  have hlea : G.IsLink (cd.edge ⟨0, by omega⟩) (cd.vtx ⟨1, by omega⟩) (cd.vtx ⟨0, by omega⟩) := by
    have h := cd.link ⟨0, by omega⟩
    rw [show (⟨0, by omega⟩ : Fin cd.d).succ = (⟨1, by omega⟩ : Fin (cd.d + 1)) from Fin.ext rfl,
      show (⟨0, by omega⟩ : Fin cd.d).castSucc = (⟨0, by omega⟩ : Fin (cd.d + 1)) from Fin.ext rfl]
      at h
    exact h.symm
  have hleb : G.IsLink (cd.edge ⟨1, by omega⟩) (cd.vtx ⟨1, by omega⟩) (cd.vtx ⟨2, by omega⟩) := by
    have h := cd.link ⟨1, by omega⟩
    rwa [show (⟨1, by omega⟩ : Fin cd.d).succ = (⟨2, by omega⟩ : Fin (cd.d + 1)) from Fin.ext rfl,
      show (⟨1, by omega⟩ : Fin cd.d).castSucc = (⟨1, by omega⟩ : Fin (cd.d + 1)) from Fin.ext rfl]
      at h
  -- Distinctness from `vtx_inj`/`edge_inj`.
  have hav : cd.vtx (⟨0, by omega⟩ : Fin (cd.d + 1)) ≠ cd.vtx ⟨1, by omega⟩ :=
    cd.vtx_ne (by omega) (by omega) (by omega)
  have hbv : cd.vtx (⟨2, by omega⟩ : Fin (cd.d + 1)) ≠ cd.vtx ⟨1, by omega⟩ :=
    cd.vtx_ne (by omega) (by omega) (by omega)
  have hba : cd.vtx (⟨2, by omega⟩ : Fin (cd.d + 1)) ≠ cd.vtx ⟨0, by omega⟩ :=
    cd.vtx_ne (by omega) (by omega) (by omega)
  have heab : cd.edge (⟨0, by omega⟩ : Fin cd.d) ≠ cd.edge ⟨1, by omega⟩ := fun h => by
    have := congrArg Fin.val (cd.edge_inj h); simp only at this; omega
  -- The base body's degree-2 closure: every `G`-edge at `vtx 1` is `edge 0` or `edge 1`. The base
  -- body `vtx 1 = vtx (⟨1, _⟩ : Fin cd.d).castSucc`, so `deg_two_split` at the interior index 1
  -- names the pair `{edge 1, edge (1−1) = edge 0}`; reorder to `{edge 0, edge 1}`.
  have hclv : ∀ e x, G.IsLink e (cd.vtx (⟨1, by omega⟩ : Fin (cd.d + 1))) x →
      e = cd.edge ⟨0, by omega⟩ ∨ e = cd.edge ⟨1, by omega⟩ := by
    intro e x hlink
    have hcast : (⟨1, by omega⟩ : Fin cd.d).castSucc = (⟨1, by omega⟩ : Fin (cd.d + 1)) :=
      Fin.ext rfl
    have h := cd.deg_two_split (i := ⟨1, by omega⟩) (by simp) e x (by rwa [hcast])
    rcases h with h | h
    · exact Or.inr h
    · refine Or.inl ?_
      rwa [show (⟨(1 : ℕ) - 1, by omega⟩ : Fin cd.d) = ⟨0, by omega⟩ from rfl] at h
  -- The eq.-(6.22) nested-IH rank bound at the base split, the discriminator's `h622lb` slot.
  have h622lb := PanelHingeFramework.case_III_nested_rank_lower_all_k hk1 hn G
    (cd.vtx ⟨1, by omega⟩) (cd.vtx ⟨0, by omega⟩) (cd.vtx ⟨2, by omega⟩)
    (cd.edge ⟨0, by omega⟩) (cd.edge ⟨1, by omega⟩) cd.e₀ hG hV3 hSimple hba hav hbv heab
    hlea hleb hclv cd.e₀_fresh hIH
  -- Fire the discriminator at the base split.
  exact PanelHingeFramework.exists_shared_redundancy_and_matched_candidate cd hk1 hn
    (cd.vtx ⟨1, by omega⟩) (cd.vtx ⟨0, by omega⟩) (cd.vtx ⟨2, by omega⟩) hav hbv hba
    (cd.vtx_mem _) (cd.vtx_mem _) cd.e₀_fresh h622lb hdef_Gab hsplitGP

/-- **CHAIN-2c-iii LEAF-5 — the dispatch's interior branch** (`lem:case-III` general-`d`;
Katoh–Tanigawa 2011 §6.4.2, Lemma 6.13 the interior per-`i` arm; Phase 23f). The load-bearing
core of the chain dispatch `chainData_dispatch`: at a **matched interior candidate** `i` (`2 ≤ i`,
`3 ≤ cd.d`), it wires the honest interior arm `chainData_interior_realization_hρGv` to all its
per-slot suppliers from the base-`v₁`-split data the discriminator
(`exists_shared_redundancy_and_matched_candidate`) produces, with the **full-`G`-link recording**
selector `ends₀` already in hand (the discriminator's `ends` overridden at the two base-body chain
hinges `edge 0`/`edge 1` so it records *every* `G`-link, the
`fullLink_recording_of_splitOff_recording` shape; the override construction + the `congr_ends`
transfer of the discriminator facts to `ends₀` is the router's mechanical plumbing, the `ends₁`
pattern of `chainData_split_realization`). The router (`chainData_dispatch`) fires the
discriminator once at the base split and case-splits `(i : ℕ)`: the base candidate (`i ≤ 1`) + the
`d = 3` floor route to the LANDED `chainData_split_realization`; this lemma is the `2 ≤ i` arm.

Inputs (all at the honest base selector `ends₀`, the discriminator's outputs transferred there):
* `hrec_G`/`he₀rec` — `ends₀` records every `G`-link + the normalized `e₀`-orientation `(v₂, v₀)`;
* `hρ₀ne`/`hρ₀e₀` — the shared redundancy `ρ₀ ≠ 0` annihilates the base chain panel `C(v₀, v₂)`;
* `hw`/`hwmem'` — the W6b bottom family `w` (each a genuine `G − v₁`-row or an `(v₀v₂)`-block tag);
* `hedgeGv` — the eq.-(6.66) edge-grouped `G − v₁`-row widening of `hingeRow v₀ v₂ ρ₀`;
* `hLI`/`hgate` — the matched-candidate discriminator gate at `candidateVtx i = vtx i.succ`;
* `hρ₀Gv` — (B′) the genuine base redundancy span at `ends₀`.

Every per-slot supplier is landed: `fullLink_recording_of_splitOff_recording` (the `hρGv` leaf's
`hrec`, fed `hrec_G`), `chainData_relabel_arm_hρGv` (the crux `±r` membership),
`interior_hρe₀_of_baseWidening` (the splice annihilation `hρe₀`), `chainData_bottom_relabel` (the
relabel-image bottom family), and `candidateEnds_records_splitOff_isLink` (the selector recording).
Below the C.0–C.6 contract + 0-dof motive; no cert change, no new linear algebra. No `\lean` pin
(internal infra; the chain dispatch carries the blueprint node). -/
theorem PanelHingeFramework.chainData_dispatch_interior
    [Finite α] [Finite β]
    {G : Graph α β} {n : ℕ} (cd : G.ChainData n) (h3 : 3 ≤ cd.d) (hSimple : G.Simple)
    (i : Fin cd.d) (h2i : 2 ≤ (i : ℕ))
    {q : α × Fin (k + 2) → ℝ} {ends₀ : β → α × α}
    {ρ₀ : Module.Dual ℝ (ScrewSpace k)}
    {ιb : Type*} [Finite ιb] {w : ιb → Module.Dual ℝ (α → ScrewSpace k)}
    (hwcard : Nat.card ιb = screwDim k * (V(G).ncard - 2))
    {n' : Fin (k + 2) → ℝ}
    (hgp_seed : ∀ x y : α, x ≠ y → LinearIndependent ℝ ![fun j => q (x, j), fun j => q (y, j)])
    (hrec_G : ∀ f x y, G.IsLink f x y → ends₀ f = (x, y) ∨ ends₀ f = (y, x))
    (he₀rec : ends₀ cd.e₀ = (cd.vtx ⟨2, by omega⟩, cd.vtx ⟨0, by omega⟩))
    (hρ₀e₀ : ρ₀ (panelSupportExtensor (fun j => q (cd.vtx ⟨0, by omega⟩, j))
      (fun j => q (cd.vtx ⟨2, by omega⟩, j))) = 0)
    (hw : LinearIndependent ℝ w)
    (hwmem' : ∀ j, w j ∈ (PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx ⟨1, by omega⟩))
        ends₀ q).toBodyHinge.rigidityRows ∨
      ∃ ρ' : Module.Dual ℝ (ScrewSpace k),
        ρ' (panelSupportExtensor (fun j => q (cd.vtx ⟨0, by omega⟩, j))
          (fun j => q (cd.vtx ⟨2, by omega⟩, j))) = 0 ∧
        w j = BodyHingeFramework.hingeRow (cd.vtx ⟨0, by omega⟩) (cd.vtx ⟨2, by omega⟩) ρ')
    (hedgeGv :
      ∃ (nGv : ℕ) (cGv : Fin nGv → ℝ) (evGv : Fin nGv → β) (uvGv vvGv : Fin nGv → α)
          (rvGv : Fin nGv → Module.Dual ℝ (ScrewSpace k)),
        (∀ j, (G.removeVertex (cd.vtx ⟨1, by omega⟩)).IsLink (evGv j) (uvGv j) (vvGv j)) ∧
        (∀ j, rvGv j ∈ (PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx ⟨1, by omega⟩))
          ends₀ q).toBodyHinge.hingeRowBlock (evGv j)) ∧
        BodyHingeFramework.hingeRow (cd.vtx ⟨0, by omega⟩) (cd.vtx ⟨2, by omega⟩) ρ₀
          = ∑ j, cGv j • BodyHingeFramework.hingeRow (uvGv j) (vvGv j) (rvGv j))
    (hLI : LinearIndependent ℝ ![fun j => q (cd.candidateVtx i, j), n'])
    (hgate : ρ₀ (panelSupportExtensor (fun j => q (cd.candidateVtx i, j)) n') ≠ 0)
    (hρ₀Gv : BodyHingeFramework.hingeRow (cd.vtx ⟨0, by omega⟩) (cd.vtx ⟨2, by omega⟩) ρ₀ ∈
      Submodule.span ℝ (PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx ⟨1, by omega⟩))
        ends₀ q).toBodyHinge.rigidityRows)
    (hdef : G.deficiency n = 0) :
    PanelHingeFramework.HasGenericFullRankRealization k n G := by
  classical
  haveI : Fintype α := Fintype.ofFinite α
  have h0i : 0 < (i : ℕ) := by omega
  have hid : (i : ℕ) < cd.d := i.isLt
  -- The interior-split tuple `(v, a, b, e_a, e_b)` and seed `qρ`.
  set v := cd.vtx i.castSucc with hv
  set a := cd.vtx i.succ with ha
  set b := cd.vtx (⟨(i : ℕ) - 1, by omega⟩ : Fin cd.d).castSucc with hb
  set e_a := cd.edge i with hea
  set e_b := cd.edge ⟨(i : ℕ) - 1, by omega⟩ with heb
  set qρ : α × Fin (k + 2) → ℝ := fun p => q (cd.shiftPerm i.castSucc p.1, p.2) with hqρ
  set Gv := G.removeVertex v with hGv
  haveI hGloop : G.Loopless := hSimple.toLoopless
  haveI : Gv.Loopless := hGloop.mono (hGv ▸ Graph.removeVertex_le G v)
  -- The two chain edges out of `v`, their distinctness.
  have hlea : G.IsLink e_a v a := cd.isLink_succ_edge i
  have hleb : G.IsLink e_b v b := cd.isLink_pred_edge h0i
  have heab : e_a ≠ e_b := (cd.pred_edge_ne h0i).symm
  -- The crux leaf's full-`G`-link recording specialised at `e₀` (head `s = 0` of the perp).
  have hrece₀ : ends₀ cd.e₀ = (cd.vtx ⟨0, by omega⟩, cd.vtx ⟨2, by omega⟩) ∨
      ends₀ cd.e₀ = (cd.vtx ⟨2, by omega⟩, cd.vtx ⟨0, by omega⟩) := Or.inr he₀rec
  -- (1) the splice annihilation `hρe₀` at `e₀`, in the un-relabelled base framework: `ρ₀` kills the
  -- `e₀` support extensor (`he₀rec` gives the `(v₂, v₀)` orientation; `panelSupportExtensor_swap`
  -- absorbs the sign, then `hρ₀e₀`).
  have hρe₀base : ρ₀ ((PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx ⟨1, by omega⟩))
      ends₀ q).toBodyHinge.supportExtensor cd.e₀) = 0 := by
    rw [PanelHingeFramework.toBodyHinge_supportExtensor, PanelHingeFramework.ofNormals_normal,
      PanelHingeFramework.ofNormals_normal, PanelHingeFramework.ofNormals_ends, he₀rec,
      panelSupportExtensor_swap, map_neg, hρ₀e₀, neg_zero]
  -- (2) the eq.-(6.66) interior `hρe₀` slot, from the base widening bundle + the matched chain-edge
  -- orientation (read off `hrec_G` at `edge i`, which links `v = vtx i.castSucc` to `a`).
  have hends_i : ends₀ e_a = (a, v) ∨ ends₀ e_a = (v, a) := by
    rcases hrec_G e_a v a hlea with h | h
    · exact Or.inr h
    · exact Or.inl h
  have hρe₀ : ρ₀ (panelSupportExtensor (fun j => qρ (a, j)) (fun j => qρ (b, j))) = 0 :=
    cd.interior_hρe₀_of_baseWidening h3 i h2i ends₀ hends_i hedgeGv
  -- (3) the crux `±r` membership `hingeRow a b (-ρ₀) ∈ span (ofNormals Gv ends₀ qρ)` — the landed
  -- crux leaf, fed the full-`G` recording `hrec_G` + the base redundancy `hρ₀Gv` + the widening.
  obtain ⟨nGv, cGv, evGv, uvGv, vvGv, rvGv, hlinkGv, hrvGv, hcombGv⟩ := hedgeGv
  have hρGv : BodyHingeFramework.hingeRow a b (-ρ₀) ∈ Submodule.span ℝ
      (PanelHingeFramework.ofNormals Gv ends₀ qρ).toBodyHinge.rigidityRows := by
    refine cd.chainData_relabel_arm_hρGv h3 i h2i cGv evGv uvGv vvGv rvGv hrec_G hrece₀
      (fun j => (Graph.removeVertex_isLink.mp (hlinkGv j)).1) hrvGv hcombGv.symm ?_ hρ₀Gv hρe₀base
    -- `hdeg1`: a summand incident to `vtx 2` uses `edge 2` (the `interior_hρe₀_of_baseWidening`
    -- argument, lifted from `removeVertex`-links to `G`-edges).
    intro j hj
    obtain ⟨hGlink, hu1, hv1⟩ := Graph.removeVertex_isLink.mp (hlinkGv j)
    have hlink_one : G.IsLink (cd.edge ⟨1, by omega⟩) (cd.vtx ⟨1, by omega⟩)
        (cd.vtx ⟨2, by omega⟩) := by
      have h := cd.link ⟨1, by omega⟩
      rwa [show (⟨1, by omega⟩ : Fin cd.d).castSucc = (⟨1, by omega⟩ : Fin (cd.d + 1)) from
          Fin.ext rfl,
        show (⟨1, by omega⟩ : Fin cd.d).succ = (⟨2, by omega⟩ : Fin (cd.d + 1)) from Fin.ext rfl]
        at h
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
  -- (4) the base-split recording the arm's `hrec'` slot wants (a specialisation of `hrec_G`).
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
    · -- `f = e₀`: `{x, y} = {vtx 2, vtx 0}`; record from `he₀rec : ends₀ e₀ = (vtx 2, vtx 0)`.
      rw [hidx10, hidx00] at hxy
      rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl he₀rec
      · exact Or.inr he₀rec
  -- The override selector `endsσρ₁` = `ends₀` overridden at the two interior chain hinges.
  set endsσρ₁ : β → α × α := Function.update (Function.update ends₀ e_a (v, a)) e_b (v, b)
    with hendsσρ₁
  have hoff : ∀ e, e ≠ e_a → e ≠ e_b → endsσρ₁ e = ends₀ e := by
    intro e hea heb
    rw [hendsσρ₁, Function.update_of_ne heb, Function.update_of_ne hea]
  have hends_ea : endsσρ₁ e_a = (v, a) := by
    rw [hendsσρ₁, Function.update_of_ne heab, Function.update_self]
  have hends_eb : endsσρ₁ e_b = (v, b) := by rw [hendsσρ₁, Function.update_self]
  -- `Gv`-link survivors and the override's recording of them.
  have hGv_off : ∀ {e u w}, Gv.IsLink e u w → e ≠ e_a ∧ e ≠ e_b := by
    intro e u w hlink
    rw [hGv, Graph.removeVertex_isLink] at hlink
    obtain ⟨hGlink, hunev, hwnev⟩ := hlink
    refine ⟨fun he => ?_, fun he => ?_⟩
    · subst he
      rcases hlea.eq_and_eq_or_eq_and_eq hGlink with ⟨hh, _⟩ | ⟨hh, _⟩
      · exact hunev hh.symm
      · exact hwnev hh.symm
    · subst he
      rcases hleb.eq_and_eq_or_eq_and_eq hGlink with ⟨hh, _⟩ | ⟨hh, _⟩
      · exact hunev hh.symm
      · exact hwnev hh.symm
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
      -- `qρ` pairs are LI: `qρ (x,·) = q (ρ x, ·)`, and `ρ` is injective, so `ρ x ≠ ρ y`.
      exact hgp_seed (cd.shiftPerm i.castSucc x) (cd.shiftPerm i.castSucc y)
        ((cd.shiftPerm i.castSucc).injective.ne hxy)
    · rw [PanelHingeFramework.ofNormals_ends]; exact hlink.ne
  -- The bottom family relabelled along `L`, and its independence (the M₃ `hw.map'` pattern).
  set L : Module.Dual ℝ (α → ScrewSpace k) →ₗ[ℝ] Module.Dual ℝ (α → ScrewSpace k) :=
    (LinearMap.funLeft ℝ (ScrewSpace k) (cd.shiftPerm i.castSucc).symm).dualMap with hL
  have hwL : LinearIndependent ℝ (fun j => L (w j)) :=
    hw.map' _ (LinearMap.ker_eq_bot.2
      (LinearMap.dualMap_injective_of_surjective
        (LinearMap.funLeft_surjective_of_injective _ _ (cd.shiftPerm i.castSucc).symm
          (Equiv.injective _))))
  -- `ends₀` records every `removeVertex (vtx 1)`-link (for `chainData_bottom_relabel`'s `hrec`).
  have hrec_Gv1 : ∀ e x y, (G.removeVertex (cd.vtx (⟨1, by omega⟩ : Fin cd.d).castSucc)).IsLink
      e x y → ends₀ e = (x, y) ∨ ends₀ e = (y, x) :=
    fun e x y hlink => hrec_G e x y (Graph.removeVertex_isLink.mp hlink).1
  -- The `vtx`-index `.castSucc` normalizations (the supplier states the base split at `Fin cd.d`
  -- indices `.castSucc`-injected; the discriminator's outputs use the bare `Fin (cd.d+1)` indices).
  have hv0c : cd.vtx (⟨0, by omega⟩ : Fin cd.d).castSucc = cd.vtx ⟨0, by omega⟩ :=
    congrArg cd.vtx (Fin.ext rfl)
  have hv2c : cd.vtx (⟨2, by omega⟩ : Fin cd.d).castSucc = cd.vtx ⟨2, by omega⟩ :=
    congrArg cd.vtx (Fin.ext rfl)
  -- Normalize the discriminator's bottom family to the `(v₂, v₀)`-block-tag orientation the
  -- supplier `chainData_bottom_relabel` keys to (the d=3 `case_III_candidate_dispatch:460–490`
  -- `ρ' → -ρ'` flip: `hingeRow v₀ v₂ ρ' = hingeRow v₂ v₀ (-ρ')`, the perp swap-invariant).
  have hwmem_norm : ∀ j, w j ∈ (PanelHingeFramework.ofNormals
        (G.removeVertex (cd.vtx (⟨1, by omega⟩ : Fin cd.d).castSucc)) ends₀
        q).toBodyHinge.rigidityRows
      ∨ ∃ ρ' : Module.Dual ℝ (ScrewSpace k),
        ρ' (panelSupportExtensor (fun j => q (cd.vtx (⟨2, by omega⟩ : Fin cd.d).castSucc, j))
          (fun j => q (cd.vtx (⟨0, by omega⟩ : Fin cd.d).castSucc, j))) = 0 ∧
        w j = BodyHingeFramework.hingeRow (cd.vtx (⟨2, by omega⟩ : Fin cd.d).castSucc)
          (cd.vtx (⟨0, by omega⟩ : Fin cd.d).castSucc) ρ' := by
    intro j
    rcases hwmem' j with hgen | ⟨ρ', hρ'e₀, hwj⟩
    · exact Or.inl hgen
    · -- flip the tag from `(v₀, v₂)` to `(v₂, v₀)` via `ρ' → -ρ'`.
      refine Or.inr ⟨-ρ', ?_, ?_⟩
      · rw [hv0c, hv2c, LinearMap.neg_apply, panelSupportExtensor_swap, map_neg, hρ'e₀,
          neg_zero, neg_zero]
      · rw [hwj, hv0c, hv2c, BodyHingeFramework.hingeRow_swap]
  -- Gate fact at the matched candidate `i` (rewrite `candidateVtx i = vtx i.succ = a`).
  have hcandVtx : cd.candidateVtx i = a := cd.candidateVtx_succ_eq h0i
  -- Wire the honest interior arm.
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
    -- per-member, via `chainData_bottom_relabel` (the relabel-image bottom family at
    -- `candidateEnds i ends₀`); the arm bridges it to the engine override `endsσρ₁` internally.
    -- The `1 < i` is pulled out of the call so `exact` stays syntactic (TACTICS-QUIRKS §43).
    intro j
    have hi1 : 1 < (i : ℕ) := by omega
    have he₀rec' : ends₀ cd.e₀ = (cd.vtx (⟨2, by omega⟩ : Fin cd.d).castSucc,
        cd.vtx (⟨0, by omega⟩ : Fin cd.d).castSucc) := by rw [hv2c, hv0c]; exact he₀rec
    exact PanelHingeFramework.chainData_bottom_relabel cd i hi1 hrec_Gv1 he₀rec' (hwmem_norm j)

/-- **CHAIN-2c-iii LEAF-5 — the dispatch's interior branch, fed the raw discriminator output**
(`lem:case-III` general-`d`; Katoh–Tanigawa 2011 §6.4.2, Lemma 6.13 the interior per-`i` arm; Phase
23f). The interior arm of the chain dispatch `chainData_dispatch`, taking the base-`v₁`-split
discriminator (`exists_shared_redundancy_and_matched_candidate`) output VERBATIM — at the honest
base selector `ends` (the `Gab`-recording, not yet the full-`G`-recording override) — and producing
`HasGenericFullRankRealization k n G` at a matched interior candidate `i` (`2 ≤ i`, `3 ≤ cd.d`).

This is the `ends → ends₀` SELECTOR-OVERRIDE + fact-transfer half of the router (the "`ends₁`
mechanical plumbing"), composed with the landed `chainData_dispatch_interior` (which takes the
overridden `ends₀`). It builds `ends₀ := Function.update³ ends` overriding the three edges the
discriminator's `Gab`-recording does not orient as the crux leaf wants — the base body `vtx 1`'s two
degree-2 chain edges `edge 0`/`edge 1` (the missing `G`-edges, so `ends₀` records every `G`-link via
`fullLink_recording_of_splitOff_recording`) and the splice `e₀` (normalized to `(vtx 2, vtx 0)` for
`he₀rec`). All three overridden edges LINK the removed base body `vtx 1`, so none is a
`Gv = G − vtx 1`-link, and `ends₀` agrees with `ends` on every `Gv`-link
(`rigidityRows_ofNormals_congr_ends`). Hence the discriminator's `Gv`-stated facts — the bottom
family `hwmem'`, the eq.-(6.66) widening `hedgeGv`, and the (B′) base redundancy `hρ₀Gv` — transfer
to `ends₀` unchanged, and the `e₀`-panel annihilation `hρ₀e₀` / the matched gate `hLI`/`hgate` are
selector-free. The discriminator's `hrecGab` (the full `Gab`-link recording) plus the chain-edge /
splice orientations (read off `ends₀`'s own override values + `cd.link`) feed the full-`G`
recording. Then `chainData_dispatch_interior` does the substantive arm assembly.

Below the C.0–C.6 contract + 0-dof motive; no cert change, no new linear algebra. No `\lean` pin
(internal infra; the chain dispatch carries the blueprint node). -/
theorem PanelHingeFramework.chainData_dispatch_interior_of_discriminator
    [Finite α] [Finite β]
    {G : Graph α β} {n : ℕ} (cd : G.ChainData n) (h3 : 3 ≤ cd.d) (hSimple : G.Simple)
    (i : Fin cd.d) (h2i : 2 ≤ (i : ℕ))
    {q : α × Fin (k + 2) → ℝ} {ends : β → α × α}
    {ρ₀ : Module.Dual ℝ (ScrewSpace k)}
    {w : Fin (screwDim k * (V(G.splitOff (cd.vtx ⟨1, by omega⟩) (cd.vtx ⟨0, by omega⟩)
          (cd.vtx ⟨2, by omega⟩) cd.e₀).ncard - 1)) → Module.Dual ℝ (α → ScrewSpace k)}
    {n' : Fin (k + 2) → ℝ}
    -- The discriminator's output bundle (at the base split `(v, a, b) = (vtx 1, vtx 0, vtx 2)`,
    -- honest base selector `ends`), the `exists_shared_redundancy_and_matched_candidate` shape:
    (hgp : (PanelHingeFramework.ofNormals (G.splitOff (cd.vtx ⟨1, by omega⟩) (cd.vtx ⟨0, by omega⟩)
      (cd.vtx ⟨2, by omega⟩) cd.e₀) ends q).IsGeneralPosition)
    (hρ₀e₀ : ρ₀ (panelSupportExtensor (fun j => q (cd.vtx ⟨0, by omega⟩, j))
      (fun j => q (cd.vtx ⟨2, by omega⟩, j))) = 0)
    (hw : LinearIndependent ℝ w)
    (hwmem' : ∀ j, w j ∈ (PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx ⟨1, by omega⟩))
        ends q).toBodyHinge.rigidityRows ∨
      ∃ ρ' : Module.Dual ℝ (ScrewSpace k),
        ρ' (panelSupportExtensor (fun j => q (cd.vtx ⟨0, by omega⟩, j))
          (fun j => q (cd.vtx ⟨2, by omega⟩, j))) = 0 ∧
        w j = BodyHingeFramework.hingeRow (cd.vtx ⟨0, by omega⟩) (cd.vtx ⟨2, by omega⟩) ρ')
    (hedgeGv :
      ∃ (nGv : ℕ) (cGv : Fin nGv → ℝ) (evGv : Fin nGv → β) (uvGv vvGv : Fin nGv → α)
          (rvGv : Fin nGv → Module.Dual ℝ (ScrewSpace k)),
        (∀ j, (G.removeVertex (cd.vtx ⟨1, by omega⟩)).IsLink (evGv j) (uvGv j) (vvGv j)) ∧
        (∀ j, rvGv j ∈ (PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx ⟨1, by omega⟩))
          ends q).toBodyHinge.hingeRowBlock (evGv j)) ∧
        BodyHingeFramework.hingeRow (cd.vtx ⟨0, by omega⟩) (cd.vtx ⟨2, by omega⟩) ρ₀
          = ∑ j, cGv j • BodyHingeFramework.hingeRow (uvGv j) (vvGv j) (rvGv j))
    (hLI : LinearIndependent ℝ ![fun j => q (cd.candidateVtx i, j), n'])
    (hgate : ρ₀ (panelSupportExtensor (fun j => q (cd.candidateVtx i, j)) n') ≠ 0)
    (hρ₀Gv : BodyHingeFramework.hingeRow (cd.vtx ⟨0, by omega⟩) (cd.vtx ⟨2, by omega⟩) ρ₀ ∈
      Submodule.span ℝ (PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx ⟨1, by omega⟩))
        ends q).toBodyHinge.rigidityRows)
    (hrecGab : ∀ f x y, (G.splitOff (cd.vtx ⟨1, by omega⟩) (cd.vtx ⟨0, by omega⟩)
        (cd.vtx ⟨2, by omega⟩) cd.e₀).IsLink f x y → ends f = (x, y) ∨ ends f = (y, x))
    (hdef : G.deficiency n = 0) :
    PanelHingeFramework.HasGenericFullRankRealization k n G := by
  classical
  haveI : Fintype α := Fintype.ofFinite α
  haveI hGloop : G.Loopless := hSimple.toLoopless
  -- The three chain-vertex names (bare `Fin (cd.d+1)` indices, as the interior branch states them).
  -- They are NOT `set`-abbreviated: `w`'s type mentions `cd.vtx ⟨0/1/2, _⟩`, so `set` would shadow
  -- the discriminator's `w`-stated hypotheses (`hw`/`hwmem'`) against the final `exact`.
  set Gv := G.removeVertex (cd.vtx (⟨1, by omega⟩ : Fin (cd.d + 1))) with hGv
  -- The base body's two degree-2 chain edges and the splice, as `G`-links (`edge 0` links v₀–v₁,
  -- `edge 1` links v₁–v₂). These are the three edges where `ends₀` overrides `ends`; each links
  -- the removed base body `v₁`, so none is a `Gv`-link.
  have hl0 : G.IsLink (cd.edge ⟨0, by omega⟩) (cd.vtx ⟨0, by omega⟩) (cd.vtx ⟨1, by omega⟩) := by
    have h := cd.link ⟨0, by omega⟩
    rwa [show (⟨0, by omega⟩ : Fin cd.d).succ = (⟨1, by omega⟩ : Fin (cd.d + 1)) from Fin.ext rfl,
      show (⟨0, by omega⟩ : Fin cd.d).castSucc = (⟨0, by omega⟩ : Fin (cd.d + 1)) from Fin.ext rfl]
      at h
  have hl1 : G.IsLink (cd.edge ⟨1, by omega⟩) (cd.vtx ⟨1, by omega⟩) (cd.vtx ⟨2, by omega⟩) := by
    have h := cd.link ⟨1, by omega⟩
    rwa [show (⟨1, by omega⟩ : Fin cd.d).succ = (⟨2, by omega⟩ : Fin (cd.d + 1)) from Fin.ext rfl,
      show (⟨1, by omega⟩ : Fin cd.d).castSucc = (⟨1, by omega⟩ : Fin (cd.d + 1)) from Fin.ext rfl]
      at h
  have he₀ne0 : cd.e₀ ≠ cd.edge ⟨0, by omega⟩ := fun h =>
    cd.e₀_fresh (h ▸ hl0.edge_mem)
  have he₀ne1 : cd.e₀ ≠ cd.edge ⟨1, by omega⟩ := fun h =>
    cd.e₀_fresh (h ▸ hl1.edge_mem)
  have he01 : cd.edge ⟨0, by omega⟩ ≠ cd.edge ⟨1, by omega⟩ := fun h => by
    have := congrArg Fin.val (cd.edge_inj h); simp only at this; omega
  -- THE FULL-`G`-RECORDING OVERRIDE `ends₀`: `ends` overridden at the splice `e₀ ↦ (v₂, v₀)` and
  -- the two base-body chain edges `edge 0 ↦ (v₀, v₁)`, `edge 1 ↦ (v₁, v₂)`.
  set ends₀ : β → α × α :=
    Function.update (Function.update (Function.update ends cd.e₀
        (cd.vtx ⟨2, by omega⟩, cd.vtx ⟨0, by omega⟩))
      (cd.edge ⟨0, by omega⟩) (cd.vtx ⟨0, by omega⟩, cd.vtx ⟨1, by omega⟩))
      (cd.edge ⟨1, by omega⟩) (cd.vtx ⟨1, by omega⟩, cd.vtx ⟨2, by omega⟩) with hends₀
  -- The override values (`Function.update_self` / `_of_ne` reductions).
  have he₀rec : ends₀ cd.e₀ = (cd.vtx ⟨2, by omega⟩, cd.vtx ⟨0, by omega⟩) := by
    rw [hends₀, Function.update_of_ne he₀ne1, Function.update_of_ne he₀ne0,
      Function.update_self]
  have hr0 : ends₀ (cd.edge ⟨0, by omega⟩) = (cd.vtx ⟨0, by omega⟩, cd.vtx ⟨1, by omega⟩) := by
    rw [hends₀, Function.update_of_ne he01, Function.update_self]
  have hr1 : ends₀ (cd.edge ⟨1, by omega⟩) = (cd.vtx ⟨1, by omega⟩, cd.vtx ⟨2, by omega⟩) := by
    rw [hends₀, Function.update_self]
  -- `ends₀` agrees with `ends` off the three overridden edges.
  have hoff : ∀ e, e ≠ cd.e₀ → e ≠ cd.edge ⟨0, by omega⟩ → e ≠ cd.edge ⟨1, by omega⟩ →
      ends₀ e = ends e := by
    intro e he₀ hea heb
    rw [hends₀, Function.update_of_ne heb, Function.update_of_ne hea, Function.update_of_ne he₀]
  -- Every `Gv = G − v₁`-link misses all three overridden edges (each links `v₁ ∉ V(Gv)` or is the
  -- fresh splice `e₀ ∉ E(G)`).
  have hGv_off : ∀ {e u w}, Gv.IsLink e u w →
      e ≠ cd.e₀ ∧ e ≠ cd.edge ⟨0, by omega⟩ ∧ e ≠ cd.edge ⟨1, by omega⟩ := by
    intro e u w hlink
    rw [hGv, Graph.removeVertex_isLink] at hlink
    obtain ⟨hGlink, hunev, hwnev⟩ := hlink
    refine ⟨fun he => cd.e₀_fresh (he ▸ hGlink.edge_mem), fun he => ?_, fun he => ?_⟩
    · subst he
      rcases hl0.eq_and_eq_or_eq_and_eq hGlink with ⟨_, hh⟩ | ⟨_, hh⟩
      · exact hwnev hh.symm
      · exact hunev hh.symm
    · subst he
      rcases hl1.eq_and_eq_or_eq_and_eq hGlink with ⟨hh, _⟩ | ⟨hh, _⟩
      · exact hunev hh.symm
      · exact hwnev hh.symm
  -- `ends₀ = ends` on every `Gv`-link, so the two frameworks have equal rigidity rows / hinge-row
  -- blocks there — the discriminator's `Gv`-facts transfer to `ends₀` unchanged.
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
  -- (a) the full `G`-link recording at `ends₀` (`fullLink_recording_of_splitOff_recording`): the
  -- `Gab`-recording at `ends₀` (from `hrecGab`, `e₀` orientation absorbed) + the chain-edge orders.
  have hrecGab' : ∀ f x y, (G.splitOff (cd.vtx (⟨1, by omega⟩ : Fin cd.d).castSucc)
      (cd.vtx (⟨0, by omega⟩ : Fin cd.d).castSucc) (cd.vtx (⟨2, by omega⟩ : Fin cd.d).castSucc)
      cd.e₀).IsLink f x y → ends₀ f = (x, y) ∨ ends₀ f = (y, x) := by
    intro f x y hlink
    -- normalize the `.castSucc` split indices to the bare ones the bundle uses.
    have hc1 : (⟨1, by omega⟩ : Fin cd.d).castSucc = (⟨1, by omega⟩ : Fin (cd.d + 1)) := Fin.ext rfl
    have hc0 : (⟨0, by omega⟩ : Fin cd.d).castSucc = (⟨0, by omega⟩ : Fin (cd.d + 1)) := Fin.ext rfl
    have hc2 : (⟨2, by omega⟩ : Fin cd.d).castSucc = (⟨2, by omega⟩ : Fin (cd.d + 1)) := Fin.ext rfl
    rw [hc1, hc0, hc2] at hlink
    -- `f` is a `Gab`-link: either a genuine surviving `G`-edge (`f ≠ e₀`) or the splice `f = e₀`.
    rw [Graph.splitOff_isLink] at hlink
    rcases hlink with ⟨hfne, hGlink, hxne, hyne⟩ | ⟨rfl, _, _, _, _, hxy⟩
    · -- genuine `G`-edge surviving the split: `f ∉ {e₀, edge 0, edge 1}` (else it would touch `v₁`,
      -- but `x, y ≠ v₁`); so `ends₀ f = ends f`, recorded by `hrecGab`.
      have hfa : f ≠ cd.edge ⟨0, by omega⟩ := by
        rintro rfl
        rcases hl0.eq_and_eq_or_eq_and_eq hGlink with ⟨_, h⟩ | ⟨_, h⟩
        · exact hyne h.symm
        · exact hxne h.symm
      have hfb : f ≠ cd.edge ⟨1, by omega⟩ := by
        rintro rfl
        rcases hl1.eq_and_eq_or_eq_and_eq hGlink with ⟨h, _⟩ | ⟨h, _⟩
        · exact hxne h.symm
        · exact hyne h.symm
      rw [hoff f hfne hfa hfb]
      exact hrecGab f x y (Graph.splitOff_isLink.mpr (Or.inl ⟨hfne, hGlink, hxne, hyne⟩))
    · -- the splice `f = e₀`: `{x, y} = {v₀, v₂}`; `ends₀ e₀ = (v₂, v₀)` matches up to order.
      rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inr he₀rec
      · exact Or.inl he₀rec
  have hrec_G : ∀ f x y, G.IsLink f x y → ends₀ f = (x, y) ∨ ends₀ f = (y, x) :=
    cd.fullLink_recording_of_splitOff_recording h3 hrecGab' (Or.inl hr0) (Or.inl hr1)
  -- (b) transfer the discriminator's `Gv`-stated facts to `ends₀`.
  have hwmem'₀ : ∀ j, w j ∈ (PanelHingeFramework.ofNormals Gv ends₀ q).toBodyHinge.rigidityRows ∨
      ∃ ρ' : Module.Dual ℝ (ScrewSpace k),
        ρ' (panelSupportExtensor (fun j => q (cd.vtx ⟨0, by omega⟩, j))
          (fun j => q (cd.vtx ⟨2, by omega⟩, j))) = 0 ∧
        w j = BodyHingeFramework.hingeRow (cd.vtx ⟨0, by omega⟩) (cd.vtx ⟨2, by omega⟩) ρ' := by
    intro j
    rcases hwmem' j with hgen | hcand
    · exact Or.inl (by rw [hrows]; exact hgen)
    · exact Or.inr hcand
  have hedgeGv₀ :
      ∃ (nGv : ℕ) (cGv : Fin nGv → ℝ) (evGv : Fin nGv → β) (uvGv vvGv : Fin nGv → α)
          (rvGv : Fin nGv → Module.Dual ℝ (ScrewSpace k)),
        (∀ j, Gv.IsLink (evGv j) (uvGv j) (vvGv j)) ∧
        (∀ j, rvGv j ∈ (PanelHingeFramework.ofNormals Gv ends₀ q).toBodyHinge.hingeRowBlock
          (evGv j)) ∧
        BodyHingeFramework.hingeRow (cd.vtx ⟨0, by omega⟩) (cd.vtx ⟨2, by omega⟩) ρ₀
          = ∑ j, cGv j • BodyHingeFramework.hingeRow (uvGv j) (vvGv j) (rvGv j) := by
    obtain ⟨nGv, cGv, evGv, uvGv, vvGv, rvGv, hlinkGv, hrvGv, hcomb⟩ := hedgeGv
    exact ⟨nGv, cGv, evGv, uvGv, vvGv, rvGv, hlinkGv,
      fun j => (hblock _ _ _ (hlinkGv j)).symm ▸ hrvGv j, hcomb⟩
  have hρ₀Gv₀ : BodyHingeFramework.hingeRow (cd.vtx ⟨0, by omega⟩) (cd.vtx ⟨2, by omega⟩) ρ₀ ∈
      Submodule.span ℝ (PanelHingeFramework.ofNormals Gv ends₀ q).toBodyHinge.rigidityRows := by
    rw [hrows]; exact hρ₀Gv
  -- (c) the seed pairwise-LI `hgp_seed`, off the discriminator's general position.
  have hgp_seed : ∀ x y : α, x ≠ y →
      LinearIndependent ℝ ![fun j => q (x, j), fun j => q (y, j)] := by
    intro x y hxy
    have := hgp x y hxy
    rwa [PanelHingeFramework.ofNormals_normal, PanelHingeFramework.ofNormals_normal] at this
  -- the `w`-carrier cardinality (`screwDim k * (V(Gab) − 1) = screwDim k * (V(G) − 2)`).
  have hcard_Gab : V(G.splitOff (cd.vtx ⟨1, by omega⟩) (cd.vtx ⟨0, by omega⟩)
      (cd.vtx ⟨2, by omega⟩) cd.e₀).ncard = V(G).ncard - 1 := by
    rw [Graph.vertexSet_splitOff,
      Set.ncard_diff_singleton_of_mem (cd.vtx_mem ⟨1, by omega⟩)]
  have hwcard : Nat.card (Fin (screwDim k *
      (V(G.splitOff (cd.vtx ⟨1, by omega⟩) (cd.vtx ⟨0, by omega⟩)
        (cd.vtx ⟨2, by omega⟩) cd.e₀).ncard - 1))) = screwDim k * (V(G).ncard - 2) := by
    rw [Nat.card_fin, hcard_Gab, Nat.sub_sub]
  -- Wire the landed interior branch on the overridden `ends₀`.
  exact PanelHingeFramework.chainData_dispatch_interior (k := k) cd h3 hSimple i h2i
    hwcard hgp_seed hrec_G he₀rec hρ₀e₀ hw hwmem'₀ hedgeGv₀ hLI hgate hρ₀Gv₀ hdef

/-- **The Case-III realization — all-`k` form** (`lem:case-III`; Katoh–Tanigawa
2011 §6.4.1, Lemma 6.10; Phase 22k L7b base, Phase 23a Leaf 4 general-`k` lift). The
`hsplitGP`-shaped producer for `theorem_55_all_k` (the all-`k` spine), at general grade `k`.

The genuinely-new Case-III chain argument — KT's fixed-3-candidate `d = 3` dispatch
(`case_III_candidate_dispatch`) replaced by the length-`d` chain dispatch + `⋀^{d−1}(ℝ^{d+1})`
duality — is **not** lifted here: it routes through the `Fin 4`/`⋀²ℝ⁴` duality (Phase 23 CHAIN, the
green-modulo boundary). 23a leaves it as the **explicit `hdispatch` hypothesis** of the producer's
`hcand`-shape (`case_III_hsplit_producer_all_k`), in the standing "carry the analytic crux as `h…`"
idiom (Phase 21b) — never a `sorry`. The `d = 3` line stays fully green through the `k = 2` wrapper
`case_III_realization` below, which fills `hdispatch` from the landed `case_III_candidate_dispatch`
(its `h622lb` slot from `case_III_nested_rank_lower`).

The body adapts the all-`k` IH to the `k = 0`-only form `case_III_hsplit_producer_all_k` expects and
threads `hdispatch` through. -/
theorem PanelHingeFramework.case_III_realization_all_k [DecidableEq β] [Finite α] [Finite β]
    {n : ℕ} (hk1 : 1 ≤ k) (hD : 6 ≤ Graph.bodyBarDim n)
    (hfresh : ∀ G' : Graph α β, ∃ e₀ : β, e₀ ∉ E(G'))
    (G : Graph α β) (hG : G.IsMinimalKDof n 0) (hV3 : 3 ≤ V(G).ncard)
    (hnoRigid : ∀ H : Graph α β, ¬ H.IsProperRigidSubgraph G n)
    (hSimple : G.Simple)
    -- All-`k` IH: `case_II_realization_all_k` shape (L5/L6 motive), dropping the `k=0`-only
    -- restriction.
    (hIH : ∀ (k' : ℤ) (G' : Graph α β), G'.IsMinimalKDof n k' → V(G').Nonempty →
      V(G').ncard < V(G).ncard →
      (G'.Simple → PanelHingeFramework.HasGenericFullRankRealization k n G') ∧
        HasPanelRealization k n G')
    -- the Case-III chain dispatch (Phase 23 CHAIN), carried as the producer's `hcand`-shaped
    -- hypothesis at general grade `k` (the green-modulo boundary; never a `sorry`).
    (hdispatch : ∀ (v a b c : α) (eₐ e_b e_c e₀ : β),
      v ∈ V(G) → a ∈ V(G) → b ∈ V(G) → c ∈ V(G) →
      a ≠ v → b ≠ v → b ≠ a → c ≠ v → c ≠ a → b ≠ c →
      eₐ ≠ e_b → eₐ ≠ e_c →
      G.IsLink eₐ v a → G.IsLink e_b v b → G.IsLink e_c a c →
      (∀ e x, G.IsLink e v x → e = eₐ ∨ e = e_b) →
      (∀ e x, G.IsLink e a x → e = eₐ ∨ e = e_c) →
      e₀ ∉ E(G) →
      (G.splitOff v a b e₀).deficiency n = 0 →
      PanelHingeFramework.HasGenericFullRankRealization k n (G.splitOff v a b e₀) →
      PanelHingeFramework.HasGenericFullRankRealization k n G) :
    PanelHingeFramework.HasGenericFullRankRealization k n G :=
  -- Adapt the all-`k` IH to the `k=0`-only form that `case_III_hsplit_producer_all_k` expects.
  PanelHingeFramework.case_III_hsplit_producer_all_k hk1 hD G hG hV3 hnoRigid hSimple
    (fun G' hG' hV2 hlt =>
      hIH 0 G' hG' ((Set.ncard_pos (Set.toFinite _)).mp (by omega)) hlt)
    hfresh hdispatch

/-- **The Case-III `d = 3` realization** (`lem:case-III`; the `k = 2` specialization of
`case_III_realization_all_k`, Phase 23a Leaf 4). Thin wrapper pinning the grade to `k = 2`, filling
the chain-dispatch hypothesis `hdispatch` from the landed `d = 3` dispatch
`case_III_candidate_dispatch` (its `h622lb` slot from `case_III_nested_rank_lower`). This keeps the
`theorem_55_all_k`/`theorem_55_minimalKDof_k` spine call site (the `hsplitZero` branch) green
unchanged through 23a; Phase 23 CHAIN discharges `hdispatch` at general `k`, ASSEMBLY threads it up
the spine. -/
theorem PanelHingeFramework.case_III_realization [DecidableEq β] [Finite α] [Finite β]
    {n : ℕ} (hD : 6 ≤ Graph.bodyBarDim n) (hn : Graph.bodyBarDim n = screwDim 2)
    (hfresh : ∀ G' : Graph α β, ∃ e₀ : β, e₀ ∉ E(G'))
    (G : Graph α β) (hG : G.IsMinimalKDof n 0) (hV3 : 3 ≤ V(G).ncard)
    (hnoRigid : ∀ H : Graph α β, ¬ H.IsProperRigidSubgraph G n)
    (hSimple : G.Simple)
    (hIH : ∀ (k' : ℤ) (G' : Graph α β), G'.IsMinimalKDof n k' → V(G').Nonempty →
      V(G').ncard < V(G).ncard →
      (G'.Simple → PanelHingeFramework.HasGenericFullRankRealization 2 n G') ∧
        HasPanelRealization 2 n G') :
    PanelHingeFramework.HasGenericFullRankRealization 2 n G :=
  PanelHingeFramework.case_III_realization_all_k (by norm_num) hD hfresh G hG hV3 hnoRigid hSimple
    hIH
    (fun v a b c eₐ e_b e_c e₀ hvG haG hbG hcG hav hbv hba hcv hca hbc heab heac
        hlea hleb hlec hclv hcla he₀ hdef_Gab hsplitGP' =>
      PanelHingeFramework.case_III_candidate_dispatch G v a b c eₐ e_b e_c e₀
        hSimple hvG haG hbG hcG hav hbv hba hcv hca hbc heab heac
        hlea hleb hlec hclv hcla he₀
        (PanelHingeFramework.case_III_nested_rank_lower hn G v a b eₐ e_b e₀
          hG hV3 hSimple hba hav hbv heab hlea hleb hclv he₀ hIH)
        hdef_Gab hG.1 hsplitGP')

end CombinatorialRigidity.Molecular
