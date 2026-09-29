/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Mathlib.Algebra.MvPolynomial.Polynomial
import CombinatorialRigidity.Molecular.Molecule.Pencil.MainComponent.Flat

/-!
# Jackson–Jordán's equality, as the `X₀` induction consumes it (Phase 40d BRIDGE)

The planar rank theorem at `(n, k) = (2, 1)` (SPINE2's non-spanning row-rank form
`PanelHingeFramework.finrank_span_rigidityRows_genuine_recordsLinks_of_theorem_55_gen`) read in
the chart `(x_v, y_v, 1)` of planar pictures, where FLAT's bridge
(`Graph.finrank_span_rigidityRows_ofNormals_pencilPicturePoint`) turns it into
Jackson–Jordán's equality `dim L(q) = 3 + def₂(G)` at the generic picture
(`blueprint/src/chapter/main-component.tex`, `sec:main-component-jj`; informal (MC-4)(c)'s
equality case, (MC-33); the consumers are (MC-141)'s list).

## Main statements

* `panelSupportExtensor_smul_right`, `PanelHingeFramework.supportExtensor_ofNormals_smul`,
  `PanelHingeFramework.infinitesimalMotions_ofNormals_smul`,
  `PanelHingeFramework.finrank_span_rigidityRows_ofNormals_smul` — rescaling every body's normal
  by a nonzero scalar rescales each hinge and leaves the motions and the rank unchanged.
* `PanelHingeFramework.finite_setOf_finrank_lt_of_curve` — **the curve-limit lemma**
  (`lem:pencil-curve-limit`, Phase 40j SPLITOFF): along a polynomial curve of normals nonzero at
  `t = 0`, the row rank drops below its value at `t = 0` for only finitely many `t`.
* `Graph.exists_mvPolynomial_le_finrank_span_rigidityRows_pencilPicturePoint` — off one nonzero
  polynomial in the picture coordinates, the plane framework at the normals `(x_v, y_v, 1)` has
  rank at least `3(|V(G)| − 1) − def₂(G)` (the chart-rank form; it carries the planar rank
  theorem's fresh-label supply `hfresh`).
* `Graph.embedEdges` — the same graph with its edges relabelled along `β ↪ β'`; it keeps `L(q)`,
  admissibility, the main pictures and every deficiency (`Graph.liftingSpace_embedEdges`,
  `Graph.isMainPicture_embedEdges_iff`, `Graph.deficiency_embedEdges`).
* `Graph.exists_mvPolynomial_finrank_liftingSpace_eq` — off one nonzero polynomial in the picture
  coordinates, the picture is main and `dim L(q) = 3 + def₂(G)` (the generic form);
  `Graph.IsMainPicture.finrank_liftingSpace_eq` (every main picture, the `ℓ₀` form) and
  `Graph.exists_isMainPicture_finrank_liftingSpace_eq` (one picture) are its corollaries.
* `Graph.x0Attains_of_deficiency_two_eq_three` — Jackson–Jordán at `G` with FLAT: when
  `def₂(G) = def₃(G)`, `X₀(G)` attains ((MC-89)'s step 3).

## Design

* **No spanning, no total selector, no `IsGenericNormals`.** The chart point comes from the
  non-spanning SPINE2 producer through the rank polynomial and the general-position polynomial
  (the `Theorem56.lean` pinch), at a common non-root that also has every third normal coordinate
  nonzero; per-body rescaling then moves it into the chart. The graph `G` sits anywhere in the
  fixed `α`, `β`, so every consumer (`H = G[W]`, `G/H`, `G′ + ab`, `G″`, `G`) is an instance.
* **Every polynomial is in the ambient picture coordinates** `α × Fin 2`, so the consumers
  multiply it with their other generic conditions.
* **No hypothesis on `β` in the Jackson–Jordán forms.** Their conclusions do not mention edge
  labels, so they relabel the edges into `β ⊕ Fin (3|α| + 1)` (`Graph.embedEdges`), where
  `Graph.freshEdgeSupply_of_card_lt (n := 2)` supplies the planar rank theorem's `hfresh`; only
  the chart-rank form, which is a statement about a framework over `β`, carries `hfresh`.
-/

open scoped Graph

namespace CombinatorialRigidity.Molecular

variable {k : ℕ}
variable {K : Type*} [Field K]
variable {α β : Type*}

/-! ## Per-body rescaling of the normals -/

/-- **The panel support extensor is homogeneous in its second normal**
(`def:panel-support-extensor`): `panelSupportExtensor n₁ (c • n₂) = c • panelSupportExtensor n₁ n₂`,
from `panelSupportExtensor_smul_left` and antisymmetry (`panelSupportExtensor_swap`). -/
theorem panelSupportExtensor_smul_right (c : K) (n₁ n₂ : Fin (k + 2) → K) :
    panelSupportExtensor n₁ (c • n₂) = c • panelSupportExtensor (k := k) n₁ n₂ := by
  rw [panelSupportExtensor_swap (c • n₂) n₁, panelSupportExtensor_smul_left,
    panelSupportExtensor_swap n₁ n₂, smul_neg, neg_neg]

/-- **Rescaling the normals rescales each hinge** (`lem:pencil-jj-rescale`): at the normals
`c_a · n_a`, the support extensor at `e` is `c_u c_v` times the one at the normals `n_a`, where
`(u, v) = ends e`. -/
theorem PanelHingeFramework.supportExtensor_ofNormals_smul (G : Graph α β) (ends : β → α × α)
    (q : α × Fin (k + 2) → K) (c : α → K) (e : β) :
    (PanelHingeFramework.ofNormals G ends (fun p => c p.1 * q p)).toBodyHinge.supportExtensor e
      = (c (ends e).1 * c (ends e).2) •
        (PanelHingeFramework.ofNormals G ends q).toBodyHinge.supportExtensor e := by
  simp only [PanelHingeFramework.toBodyHinge_supportExtensor,
    PanelHingeFramework.ofNormals_normal, PanelHingeFramework.ofNormals_ends]
  have hsm : ∀ a, (fun i => c a * q (a, i)) = c a • fun i => q (a, i) := fun a => by
    funext i; simp
  rw [hsm, hsm, panelSupportExtensor_smul_left, panelSupportExtensor_smul_right, smul_smul]

/-- **Per-body rescaling leaves the motions unchanged** (`lem:pencil-jj-rescale`): if every
`c_a` is nonzero, the framework at the normals `c_a · n_a` has the motions of the framework at
the normals `n_a`, since each hinge spans the same line
(`PanelHingeFramework.supportExtensor_ofNormals_smul`). -/
theorem PanelHingeFramework.infinitesimalMotions_ofNormals_smul (G : Graph α β)
    (ends : β → α × α) (q : α × Fin (k + 2) → K) {c : α → K} (hc : ∀ a, c a ≠ 0) :
    (PanelHingeFramework.ofNormals G ends (fun p => c p.1 * q p)).toBodyHinge.infinitesimalMotions
      = (PanelHingeFramework.ofNormals G ends q).toBodyHinge.infinitesimalMotions := by
  refine BodyHingeFramework.infinitesimalMotions_eq_of_isLink_span_supportExtensor _ _ rfl ?_
  intro e _ _ _
  rw [PanelHingeFramework.supportExtensor_ofNormals_smul]
  exact (Submodule.span_singleton_smul_eq (mul_ne_zero (hc _) (hc _)).isUnit _).symm

/-- **Per-body rescaling leaves the rank unchanged** (`lem:pencil-jj-rescale`): the rank form
of `PanelHingeFramework.infinitesimalMotions_ofNormals_smul`, through
`BodyHingeFramework.span_rigidityRows_eq_of_infinitesimalMotions_eq`. -/
theorem PanelHingeFramework.finrank_span_rigidityRows_ofNormals_smul [Finite α] (G : Graph α β)
    (ends : β → α × α) (q : α × Fin (k + 2) → K) {c : α → K} (hc : ∀ a, c a ≠ 0) :
    Module.finrank K (Submodule.span K
        (PanelHingeFramework.ofNormals G ends (fun p => c p.1 * q p)).toBodyHinge.rigidityRows)
      = Module.finrank K (Submodule.span K
          (PanelHingeFramework.ofNormals G ends q).toBodyHinge.rigidityRows) := by
  rw [BodyHingeFramework.span_rigidityRows_eq_of_infinitesimalMotions_eq _ _
    (PanelHingeFramework.infinitesimalMotions_ofNormals_smul G ends q hc)]

/-- **The curve-limit lemma** (`lem:pencil-curve-limit`; the STEPS recon's tracked spike, Phase 40j
SPLITOFF): along a polynomial curve `t ↦ c(t)` of normals, the row rank of `ofNormals G ends (c t)`
is at least its value at `t = 0` for all but finitely many `t`, provided every recorded hinge is
nonzero at `t = 0`. The univariate specialization of the rank polynomial
(`PanelHingeFramework.exists_rankPolynomial_of_le_finrank_linking`) along the curve, pulled back
through the mirror substitution lemma `MvPolynomial.polynomial_eval_aeval`: the rank polynomial
composed with the curve is a nonzero univariate polynomial (nonzero at `t = 0`), so its finitely
many roots are the only `t` where the rank can drop. -/
theorem PanelHingeFramework.finite_setOf_finrank_lt_of_curve {k : ℕ} [Finite α] [Finite β]
    (G : Graph α β) (ends : β → α × α)
    (hends : ∀ e u v, G.IsLink e u v → G.IsLink e (ends e).1 (ends e).2)
    (c : α × Fin (k + 2) → Polynomial K)
    (hne : ∀ e, G.IsLink e (ends e).1 (ends e).2 →
      (PanelHingeFramework.ofNormals G ends (fun p => (c p).eval 0)).toBodyHinge.supportExtensor e
        ≠ 0)
    {N : ℕ} (hN : N ≤ Module.finrank K (Submodule.span K
      (PanelHingeFramework.ofNormals G ends (fun p => (c p).eval 0)).toBodyHinge.rigidityRows)) :
    {t : K | Module.finrank K (Submodule.span K
      (PanelHingeFramework.ofNormals G ends (fun p => (c p).eval t)).toBodyHinge.rigidityRows)
        < N}.Finite := by
  classical
  obtain ⟨Q, hQ₀, hQ⟩ :=
    PanelHingeFramework.exists_rankPolynomial_of_le_finrank_linking G ends hends hne hN
  set P : Polynomial K := MvPolynomial.aeval c Q with hP
  have hPt : ∀ t, P.eval t = MvPolynomial.eval (fun p => (c p).eval t) Q :=
    fun t => MvPolynomial.polynomial_eval_aeval c Q t
  have hP0 : P ≠ 0 := fun h => hQ₀ (by rw [← hPt 0, h, Polynomial.eval_zero])
  refine (Polynomial.finite_setOfPred_isRoot hP0).subset fun t ht => ?_
  simp only [Set.mem_ofPred_eq] at ht
  simp only [Set.mem_ofPred_eq, Polynomial.IsRoot.def]
  by_contra h
  exact absurd (hQ _ (by rwa [← hPt])) (not_le.mpr ht)

/-! ## The planar rank theorem in the chart -/

/-- **The planar rank theorem in the chart `(x_v, y_v, 1)`** (`lem:pencil-jj-chart`; SPINE2 at
`(n, k) = (2, 1)`). For a simple graph `G` on at least two bodies, anywhere in `α` and `β`, there
are a selector `ends` recording every link and a nonzero polynomial `P` in the picture
coordinates such that at every picture `q` off the zero set of `P` the plane framework at the
normals `(x_v, y_v, 1)` has rank at least `3(|V(G)| − 1) − def₂(G)`.

Proof. The non-spanning planar rank theorem
(`PanelHingeFramework.finrank_span_rigidityRows_genuine_recordsLinks_of_theorem_55_gen`) gives a
realization `Q₀` at exactly that rank. Its rank polynomial
(`PanelHingeFramework.exists_rankPolynomial_of_le_finrank_linking`), the general-position
polynomial (`PanelHingeFramework.exists_generalPosition_polynomial`) and the product of the third
normal coordinates have a common non-root `n₀`. Rescaling each body's normal by
`n₀(a, 2)⁻¹` lands in the chart at a picture `q'`, with the same rank
(`PanelHingeFramework.finrank_span_rigidityRows_ofNormals_smul`) and nonzero hinges (general
position). The rank polynomial at `q'`, pulled back along the chart, is the required `P`. -/
theorem _root_.Graph.exists_mvPolynomial_le_finrank_span_rigidityRows_pencilPicturePoint
    [Infinite K] [Finite α] [Finite β] [DecidableEq β]
    (hfresh : ∀ (c : ℤ) (G' : Graph α β), G'.IsMinimalKDof 2 c → ∃ e₀ : β, e₀ ∉ E(G'))
    {G : Graph α β} (hSimple : G.Simple) (hV : 2 ≤ V(G).ncard) :
    ∃ (ends : β → α × α) (P : MvPolynomial (α × Fin 2) K),
      (∀ e u v, G.IsLink e u v → G.IsLink e (ends e).1 (ends e).2) ∧ P ≠ 0 ∧
      ∀ q : α × Fin 2 → K, MvPolynomial.eval q P ≠ 0 →
        screwDim 1 * ((V(G).ncard : ℤ) - 1) - G.deficiency 2 ≤
          (Module.finrank K (Submodule.span K (PanelHingeFramework.ofNormals (k := 1) G ends
            (fun p => pencilPicturePoint q p.1 p.2)).toBodyHinge.rigidityRows) : ℤ) := by
  classical
  have : Fintype α := Fintype.ofFinite α
  -- SPINE2's non-spanning planar rank theorem, at `(n, k) = (2, 1)`.
  obtain ⟨Q₀, hQ₀g, -, hQ₀ends, hQ₀C, hQ₀rank⟩ :=
    PanelHingeFramework.finrank_span_rigidityRows_genuine_recordsLinks_of_theorem_55_gen
      (K := K) (k := 1) (n := 2) le_rfl (by decide) rfl hfresh G hV hSimple
  have hself : PanelHingeFramework.ofNormals (k := 1) G Q₀.ends (fun p => Q₀.normal p.1 p.2)
      = Q₀ := by
    rw [← hQ₀g]; rfl
  set N := Module.finrank K (Submodule.span K Q₀.toBodyHinge.rigidityRows) with hN
  -- Its rank polynomial, the general-position polynomial, and the chart polynomial.
  obtain ⟨Rk, hRk₀, hRk⟩ := PanelHingeFramework.exists_rankPolynomial_of_le_finrank_linking G
    Q₀.ends hQ₀ends (q₀ := fun p => Q₀.normal p.1 p.2) (fun e _ => by rw [hself]; exact hQ₀C e)
    (N := N) (le_of_eq (by rw [hself]))
  obtain ⟨Pgp, hPgp_seed, hPgp⟩ :=
    PanelHingeFramework.exists_generalPosition_polynomial (k := 1) (K := K) G Q₀.ends
  have hRk_ne : Rk ≠ 0 := fun h => hRk₀ (by rw [h, map_zero])
  have hPgp_ne : Pgp ≠ 0 := by
    set φ : α ↪ K :=
      (Fintype.equivFin α).toEmbedding.trans (Fin.valEmbedding.trans (Infinite.natEmbedding K))
    exact fun h => hPgp_seed φ φ.injective (by rw [h, map_zero])
  have hPch_ne : (∏ a : α, MvPolynomial.X (a, (2 : Fin 3)) : MvPolynomial (α × Fin 3) K) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun a _ => MvPolynomial.X_ne_zero _
  -- A common non-root.
  obtain ⟨n₀, hn₀⟩ := MvPolynomial.exists_eval_ne_zero
    (mul_ne_zero (mul_ne_zero hRk_ne hPgp_ne) hPch_ne)
  rw [map_mul, map_mul] at hn₀
  have hn₀Rk := left_ne_zero_of_mul (left_ne_zero_of_mul hn₀)
  have hn₀gp := right_ne_zero_of_mul (left_ne_zero_of_mul hn₀)
  have hw : ∀ a, n₀ (a, 2) ≠ 0 := by
    have h := right_ne_zero_of_mul hn₀
    rw [map_prod, Finset.prod_ne_zero_iff] at h
    intro a
    simpa using h a (Finset.mem_univ a)
  -- Rescale into the chart.
  set q' : α × Fin 2 → K := fun p => (n₀ (p.1, 2))⁻¹ * n₀ (p.1, Fin.castSucc p.2) with hq'
  have hchart : (fun p : α × Fin 3 => pencilPicturePoint q' p.1 p.2)
      = fun p => (n₀ (p.1, 2))⁻¹ * n₀ p := by
    funext ⟨a, i⟩
    fin_cases i
    · simp [pencilPicturePoint, hq']
    · simp [pencilPicturePoint, hq']
    · simp [pencilPicturePoint, inv_mul_cancel₀ (hw a)]
  have hrow : Module.finrank K (Submodule.span K (PanelHingeFramework.ofNormals (k := 1) G Q₀.ends
        (fun p => pencilPicturePoint q' p.1 p.2)).toBodyHinge.rigidityRows)
      = Module.finrank K (Submodule.span K
          (PanelHingeFramework.ofNormals (k := 1) G Q₀.ends n₀).toBodyHinge.rigidityRows) := by
    rw [hchart]
    exact PanelHingeFramework.finrank_span_rigidityRows_ofNormals_smul G Q₀.ends n₀
      (c := fun a => (n₀ (a, 2))⁻¹) (fun a => inv_ne_zero (hw a))
  have hgp := hPgp n₀ hn₀gp
  have hC' : ∀ e, G.IsLink e (Q₀.ends e).1 (Q₀.ends e).2 →
      (PanelHingeFramework.ofNormals (k := 1) G Q₀.ends
        (fun p => pencilPicturePoint q' p.1 p.2)).toBodyHinge.supportExtensor e ≠ 0 := by
    intro e he
    rw [hchart, PanelHingeFramework.supportExtensor_ofNormals_smul G Q₀.ends n₀
      (fun a => (n₀ (a, 2))⁻¹)]
    refine smul_ne_zero (mul_ne_zero (inv_ne_zero (hw _)) (inv_ne_zero (hw _))) ?_
    exact PanelHingeFramework.supportExtensor_ne_zero_of_isGeneralPosition _ hgp he.ne
  -- The rank polynomial at the chart point, pulled back along the chart.
  obtain ⟨Rk₂, hRk₂₀, hRk₂⟩ := PanelHingeFramework.exists_rankPolynomial_of_le_finrank_linking G
    Q₀.ends hQ₀ends (q₀ := fun p => pencilPicturePoint q' p.1 p.2) hC' (N := N)
    (by rw [hrow]; exact hRk n₀ hn₀Rk)
  set T : MvPolynomial (α × Fin 2) K :=
    MvPolynomial.bind₁ (fun p : α × Fin 3 => pencilPicturePointPoly p.1 p.2) Rk₂ with hTdef
  have hT : ∀ q, MvPolynomial.eval q T
      = MvPolynomial.eval (fun p => pencilPicturePoint q p.1 p.2) Rk₂ := by
    intro q
    rw [hTdef, MvPolynomial.eval_bind₁]
    congr 2
    funext ⟨a, i⟩
    exact eval_pencilPicturePointPoly q a i
  refine ⟨Q₀.ends, T, hQ₀ends, fun h => hRk₂₀ (by rw [← hT, h, map_zero]), fun q hq => ?_⟩
  have hle := hRk₂ _ (by rwa [hT] at hq)
  rw [← hQ₀rank]
  exact_mod_cast hle

/-! ## Relabelling the edges into a larger label type -/

/-- **Relabel the edges of `G` along an embedding `ι : β ↪ β'`** (`lem:pencil-jj-embed-edges`):
the graph on `V(G)` with an edge `ι e` linking `x` and `y` for every link `e` of `G`. It has the
same vertices, adjacencies and closed neighbourhoods as `G`, so the lifting space, admissibility
and the deficiencies are unchanged; only the label type grows, which is what lets
Jackson–Jordán's equality be drawn from the planar rank theorem with no `β`-headroom
hypothesis. -/
def _root_.Graph.embedEdges {β' : Type*} (G : Graph α β) (ι : β ↪ β') : Graph α β' where
  vertexSet := V(G)
  IsLink e x y := ∃ e₀, ι e₀ = e ∧ G.IsLink e₀ x y
  isLink_symm := by
    rintro e -
    exact ⟨fun x y ⟨e₀, he, h⟩ => ⟨e₀, he, h.symm⟩⟩
  eq_or_eq_of_isLink_of_isLink := by
    rintro e x y v w ⟨e₀, rfl, h⟩ ⟨e₁, he, h'⟩
    obtain rfl := ι.injective he
    exact h.left_eq_or_eq h'
  left_mem_of_isLink := by
    rintro e x y ⟨e₀, -, h⟩
    exact h.left_mem

section embedEdges

variable {β' : Type*} {G : Graph α β} {ι : β ↪ β'}

/-- Relabelling keeps the bodies. -/
@[simp]
theorem _root_.Graph.vertexSet_embedEdges : V(G.embedEdges ι) = V(G) := rfl

/-- The links of the relabelled graph are the relabelled links. -/
theorem _root_.Graph.embedEdges_isLink {e : β'} {x y : α} :
    (G.embedEdges ι).IsLink e x y ↔ ∃ e₀, ι e₀ = e ∧ G.IsLink e₀ x y := Iff.rfl

/-- The edges of the relabelled graph are the relabelled edges. -/
theorem _root_.Graph.edgeSet_embedEdges : E(G.embedEdges ι) = ι '' E(G) := by
  ext e
  refine ⟨fun ⟨x, y, e₀, he, h⟩ => ⟨e₀, h.edge_mem, he⟩, ?_⟩
  rintro ⟨e₀, he₀, rfl⟩
  obtain ⟨x, y, h⟩ := G.exists_isLink_of_mem_edgeSet he₀
  exact ⟨x, y, e₀, rfl, h⟩

/-- Relabelling keeps every closed neighbourhood. -/
theorem _root_.Graph.closedNbhd_embedEdges (v : α) :
    (G.embedEdges ι).closedNbhd v = G.closedNbhd v := by
  ext w
  simp only [Graph.closedNbhd, Set.mem_ofPred_eq, Graph.embedEdges_isLink]
  constructor
  · rintro (h | ⟨-, e₀, -, h⟩)
    · exact Or.inl h
    · exact Or.inr ⟨e₀, h⟩
  · rintro (h | ⟨e₀, h⟩)
    · exact Or.inl h
    · exact Or.inr ⟨_, e₀, rfl, h⟩

/-- Relabelling keeps a simple graph simple. -/
theorem _root_.Graph.Simple.embedEdges (hG : G.Simple) : (G.embedEdges ι).Simple where
  not_isLoopAt := by
    rintro e x ⟨e₀, -, h⟩
    exact hG.toLoopless.not_isLoopAt e₀ x h
  eq_of_isLink := by
    rintro e f x y ⟨e₀, rfl, h⟩ ⟨f₀, rfl, h'⟩
    rw [hG.eq_of_isLink h h']

/-- Relabelling keeps the lifting space (`def:pencil-lifting-space`). -/
theorem _root_.Graph.liftingSpace_embedEdges (q : α × Fin 2 → K) :
    (G.embedEdges ι).liftingSpace q = G.liftingSpace q := by
  ext z
  simp only [Graph.mem_liftingSpace, Graph.vertexSet_embedEdges, Graph.closedNbhd_embedEdges]

/-- Relabelling keeps the admissible pictures (`def:pencil-admissible-picture`). -/
theorem _root_.Graph.isAdmissiblePicture_embedEdges_iff {q : α × Fin 2 → K} :
    (G.embedEdges ι).IsAdmissiblePicture q ↔ G.IsAdmissiblePicture q := by
  simp only [Graph.IsAdmissiblePicture, Graph.vertexSet_embedEdges, Graph.closedNbhd_embedEdges]
  refine and_congr_left fun _ => ⟨fun h e u v he => h (ι e) u v ⟨e, rfl, he⟩, ?_⟩
  rintro h e u v ⟨e₀, -, he⟩
  exact h e₀ u v he

/-- Relabelling keeps the dimension of the lifting space. -/
theorem _root_.Graph.finrank_liftingSpace_embedEdges (q : α × Fin 2 → K) :
    Module.finrank K ((G.embedEdges ι).liftingSpace q) = Module.finrank K (G.liftingSpace q) := by
  rw [Graph.liftingSpace_embedEdges]

/-- Relabelling keeps the main pictures (`def:pencil-main-picture`). -/
theorem _root_.Graph.isMainPicture_embedEdges_iff {q : α × Fin 2 → K} :
    (G.embedEdges ι).IsMainPicture q ↔ G.IsMainPicture q := by
  simp only [Graph.IsMainPicture, Graph.isAdmissiblePicture_embedEdges_iff,
    Graph.finrank_liftingSpace_embedEdges]

/-- Relabelling keeps every deficiency (`def:D-deficiency`): a partition crosses the images of
the edges it crossed before. -/
theorem _root_.Graph.deficiency_embedEdges (n : ℕ) :
    (G.embedEdges ι).deficiency n = G.deficiency n := by
  have hcross : ∀ f : α → α, (G.embedEdges ι).crossingEdges f = ι '' G.crossingEdges f := by
    intro f
    ext e
    simp only [Graph.crossingEdges, Graph.edgeSet_embedEdges, Graph.embedEdges_isLink,
      Set.mem_ofPred_eq, Set.mem_image]
    constructor
    · rintro ⟨⟨e₀, he₀, rfl⟩, x, y, ⟨e₁, he₁, h⟩, hxy⟩
      obtain rfl := ι.injective he₁
      exact ⟨e₁, ⟨he₀, x, y, h, hxy⟩, rfl⟩
    · rintro ⟨e₀, ⟨he₀, x, y, h, hxy⟩, rfl⟩
      exact ⟨⟨e₀, he₀, rfl⟩, x, y, ⟨e₀, rfl, h⟩, hxy⟩
  have hdef : ∀ f : α → α, (G.embedEdges ι).partitionDef n f = G.partitionDef n f := by
    intro f
    simp only [Graph.partitionDef, Graph.numParts, Graph.vertexSet_embedEdges, hcross,
      Set.ncard_image_of_injective _ ι.injective]
  simp only [Graph.deficiency, hdef]

end embedEdges

/-! ## Jackson–Jordán's equality -/

/-- A closed neighbourhood of a body of `G` lies in `V(G)`. -/
theorem _root_.Graph.closedNbhd_subset_vertexSet {G : Graph α β} {v : α} (hv : v ∈ V(G)) :
    G.closedNbhd v ⊆ V(G) := by
  rintro w (rfl | ⟨e, he⟩)
  · exact hv
  · exact he.right_mem

/-- **Jackson–Jordán's equality at the generic picture** (`thm:pencil-jj-equality`; informal
(MC-4)(c)'s equality case, (MC-33), Jackson–Jordán's pin-collinear theorem via the planar rank
theorem at `n = 2`). Let `G` be simple, with at least one body and at least three members in every
closed neighbourhood, anywhere in `α` and `β`. There is a nonzero polynomial `P` in the picture
coordinates such that every picture `q` with `P(q) ≠ 0` is a main picture with
`dim L(q) = 3 + def₂(G)`. No hypothesis on the label type: the edges are first relabelled into
`β ⊕ Fin (3|α| + 1)` (`Graph.embedEdges`), where the planar rank theorem's fresh-label supply
holds (`Graph.freshEdgeSupply_of_card_lt`), and the relabelling changes neither `L(q)`, nor the
main pictures, nor `def₂`.

Proof. The main pictures contain the non-roots of one nonzero polynomial
(`Graph.exists_mvPolynomial_isMainPicture`), and the chart-rank form
(`Graph.exists_mvPolynomial_le_finrank_span_rigidityRows_pencilPicturePoint`, at the relabelled
graph) supplies a second. At a common non-root FLAT's bridge
(`Graph.finrank_span_rigidityRows_ofNormals_pencilPicturePoint`) reads the rank as
`3|V(G)| − dim L(q)`, which gives `dim L(q) ≤ 3 + def₂(G)`; the reverse is (MC-4)(b)
(`Graph.three_add_deficiency_le_finrank_liftingSpace`). -/
theorem _root_.Graph.exists_mvPolynomial_finrank_liftingSpace_eq [Infinite K] [Finite α] [Finite β]
    {G : Graph α β} (hSimple : G.Simple) (hV : V(G).Nonempty)
    (h3 : ∀ v ∈ V(G), 3 ≤ (G.closedNbhd v).ncard) :
    ∃ P : MvPolynomial (α × Fin 2) K, P ≠ 0 ∧ ∀ q : α × Fin 2 → K, MvPolynomial.eval q P ≠ 0 →
      G.IsMainPicture q ∧ (Module.finrank K (G.liftingSpace q) : ℤ) = 3 + G.deficiency 2 := by
  classical
  -- Relabel the edges into a label type with room for the planar rank theorem.
  set ι : β ↪ β ⊕ Fin (3 * Nat.card α + 1) := Function.Embedding.inl
  set G' := G.embedEdges ι
  have hfresh : ∀ (c : ℤ) (G'' : Graph α (β ⊕ Fin (3 * Nat.card α + 1))),
      G''.IsMinimalKDof 2 c → ∃ e₀, e₀ ∉ E(G'') :=
    Graph.freshEdgeSupply_of_card_lt (by decide) (by
      rw [Nat.card_sum, Nat.card_eq_fintype_card (α := Fin _), Fintype.card_fin,
        Graph.bodyBarDim_two]
      omega)
  have hV2 : 2 ≤ V(G').ncard := by
    obtain ⟨v, hv⟩ := hV
    have := (h3 v hv).trans (Set.ncard_le_ncard (G.closedNbhd_subset_vertexSet hv) (Set.toFinite _))
    rw [Graph.vertexSet_embedEdges]
    omega
  obtain ⟨ends, Prk, hends, hPrk₀, hPrk⟩ :=
    Graph.exists_mvPolynomial_le_finrank_span_rigidityRows_pencilPicturePoint (K := K) hfresh
      hSimple.embedEdges hV2
  obtain ⟨Pmain, hPmain₀, hPmain⟩ := G.exists_mvPolynomial_isMainPicture (K := K)
    hSimple.toLoopless h3
  refine ⟨Pmain * Prk, mul_ne_zero hPmain₀ hPrk₀, fun q hq => ?_⟩
  rw [map_mul] at hq
  have hmain := hPmain q (left_ne_zero_of_mul hq)
  have hmain' : G'.IsMainPicture q := Graph.isMainPicture_embedEdges_iff.mpr hmain
  have hrk := hPrk q (right_ne_zero_of_mul hq)
  rw [Graph.finrank_span_rigidityRows_ofNormals_pencilPicturePoint hmain'.1 hends,
    screwDim_one, Graph.liftingSpace_embedEdges, Graph.deficiency_embedEdges,
    Graph.vertexSet_embedEdges] at hrk
  have hlow := Graph.three_add_deficiency_le_finrank_liftingSpace hmain.1 hV
  refine ⟨hmain, ?_⟩
  push_cast at hrk
  linarith

/-- **Jackson–Jordán's equality at every main picture** (`thm:pencil-jj-equality`; the `ℓ₀` form
of (MC-33): `ℓ₀(G) = 3 + def₂(G)`). Under the hypotheses of
`Graph.exists_mvPolynomial_finrank_liftingSpace_eq`, every main picture has
`dim L(q) = 3 + def₂(G)`: some main picture does, main pictures share the least dimension, and
(MC-4)(b) bounds it below. -/
theorem _root_.Graph.IsMainPicture.finrank_liftingSpace_eq [Infinite K] [Finite α] [Finite β]
    {G : Graph α β} (hSimple : G.Simple) (hV : V(G).Nonempty)
    (h3 : ∀ v ∈ V(G), 3 ≤ (G.closedNbhd v).ncard) {q : α × Fin 2 → K}
    (hq : G.IsMainPicture q) :
    (Module.finrank K (G.liftingSpace q) : ℤ) = 3 + G.deficiency 2 := by
  obtain ⟨P, hP₀, hP⟩ := Graph.exists_mvPolynomial_finrank_liftingSpace_eq (K := K) hSimple hV h3
  obtain ⟨q₁, hq₁⟩ := MvPolynomial.exists_eval_ne_zero hP₀
  obtain ⟨hmain₁, hdim₁⟩ := hP q₁ hq₁
  have hle : (Module.finrank K (G.liftingSpace q) : ℤ) ≤ Module.finrank K (G.liftingSpace q₁) := by
    exact_mod_cast hq.2 q₁ hmain₁.1
  have hlow := Graph.three_add_deficiency_le_finrank_liftingSpace hq.1 hV
  linarith

/-- **Jackson–Jordán's equality at one picture** (`thm:pencil-jj-equality`, the existential form):
some main picture has `dim L(q) = 3 + def₂(G)`. -/
theorem _root_.Graph.exists_isMainPicture_finrank_liftingSpace_eq [Infinite K] [Finite α]
    [Finite β] {G : Graph α β} (hSimple : G.Simple) (hV : V(G).Nonempty)
    (h3 : ∀ v ∈ V(G), 3 ≤ (G.closedNbhd v).ncard) :
    ∃ q : α × Fin 2 → K, G.IsMainPicture q ∧
      (Module.finrank K (G.liftingSpace q) : ℤ) = 3 + G.deficiency 2 := by
  obtain ⟨P, hP₀, hP⟩ := Graph.exists_mvPolynomial_finrank_liftingSpace_eq (K := K) hSimple hV h3
  obtain ⟨q, hq⟩ := MvPolynomial.exists_eval_ne_zero hP₀
  exact ⟨q, hP q hq⟩

/-- **`X₀` attains when the two deficiencies agree** (`cor:pencil-jj-flat`; informal
(MC-5)(ii) with Jackson–Jordán at `G`, (MC-89)'s step 3). A connected simple `G` with at least
three members in every closed neighbourhood and `def₂(G) = def₃(G)` has `X₀(G)` attaining:
Jackson–Jordán gives an admissible picture with `dim L(q) = 3 + def₂(G) = 3 + def₃(G)`
(`Graph.exists_isMainPicture_finrank_liftingSpace_eq`), and FLAT's flat witness
(`Graph.x0Attains_of_finrank_liftingSpace_le`) applies. -/
theorem _root_.Graph.x0Attains_of_deficiency_two_eq_three [Infinite K] [Finite α] [Finite β]
    {G : Graph α β} (hG : G.Connected) (hSimple : G.Simple)
    (h3 : ∀ v ∈ V(G), 3 ≤ (G.closedNbhd v).ncard) (hdef : G.deficiency 2 = G.deficiency 3) :
    G.X0Attains K := by
  obtain ⟨q, hq, hdim⟩ := Graph.exists_isMainPicture_finrank_liftingSpace_eq (K := K) hSimple
    hG.nonempty h3
  exact Graph.x0Attains_of_finrank_liftingSpace_le hG hq.1 (by rw [hdim, hdef])

end CombinatorialRigidity.Molecular
