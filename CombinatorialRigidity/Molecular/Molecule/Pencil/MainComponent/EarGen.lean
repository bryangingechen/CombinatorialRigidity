/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.Molecule.Pencil.MainComponent.Ear
import CombinatorialRigidity.Molecular.Molecule.Pencil.MainComponent.Lines

/-!
# An open ear over fixed base data (Phase 40h SHORT, EARGEN)

The device the open-ear steps with three and four interior bodies choose their configurations with
(`blueprint/src/chapter/main-component.tex`, `lem:pencil-ear-data`; informal (MC-180) Steps 1–2).
The data on `V₁` are fixed first — a picture `q₁`, heights `z₁`, and planes `ha`, `hb` agreeing
with `z₁` on the closed neighbourhoods of the ends `a`, `b` in `G[V₁]` — and the data of the ear
second, as a point `s` of the parameter space `(α × Fin 2) ⊕ α`: a picture point and a free height
for every body, of which only the bodies off `V₁` are read. One parametrization serves `G` and any
graph on the same bodies, such as `G` with an interior body suppressed.

## Main definitions

* `earPicture V₁ q₁ s` — the picture of ear data: `q₁` on `V₁`, the picture coordinates of `s`
  off it.
* `earHeight V₁ z₁ xf xl X ha hb q m` — the height of ear data at the picture `q`: `z₁` on `V₁`,
  the plane `ha` at the first interior body `xf`, the plane `hb` at the last `xl`, the free heights
  `m` at the other interior bodies `X`, and `0` elsewhere.
* `earConfig` — the configuration points of ear data; `earPicturePoly`, `earHeightPoly`,
  `earPointPoly` — the same data as polynomials in `s`.

## Main statements

* `eval_earPointPoly` — the configuration points of ear data are polynomial in `s`;
  `earConfig_of_mem` — on `V₁` they are those of the base data; `earConfig_of_mem_X`,
  `earConfig_first`, `earConfig_last` — the points of the interior bodies.
* `Graph.earHeight_mem_liftingSpace` — at a picture admissible for `G`, the height of ear data is
  a height of `G` (`lem:pencil-ear-data`(1)).
* `eval_bind₁_earPicturePoly` — a polynomial in the picture becomes one in the ear data
  (`lem:pencil-ear-data`(2)).
* `exists_mvPolynomial_le_finrank_ofNormals_bind`,
  `exists_mvPolynomial_le_finrank_sup_span_pointJoin` — along any polynomial parametrization of
  the configuration points, a rank lower bound (at a witness with nonzero hinges) and a lower bound
  on `dim(ρ + span of joins)` are open conditions (`lem:pencil-ear-data`(3)).

## Design

* **The ear data are a point of `K^((α × Fin 2) ⊕ α)`**, one picture pair and one height for every
  body, rather than a tuple indexed by the ear. The coordinates on `V₁` are ignored, so the same
  parameter space serves every graph on the same bodies, and substitution (`MvPolynomial.bind₁`)
  moves a polynomial in the picture or the configuration to one in the ear data.
* **The planes `ha`, `hb` are explicit.** `Graph.earExtend_mem_liftingSpace`
  (`MainComponent/Ear.lean`) hides them in an existential; here any planes agreeing with `z₁` on
  the two closed neighbourhoods serve, uniqueness unused.
-/

open scoped Graph

namespace CombinatorialRigidity.Molecular

variable {K : Type*} [Field K] {α β : Type*}

/-! ## The ear data over fixed base data -/

section EarData

variable (V₁ : Set α) (q₁ : α × Fin 2 → K) (z₁ : α → K) (xf xl : α) (X : Set α)
  (ha hb : Fin 3 → K)

open Classical in
/-- **The picture of ear data** `s` over the base picture `q₁` (`lem:pencil-ear-data`): `q₁` on
`V₁`, the picture coordinates `s (inl ·)` off it. -/
noncomputable def earPicture (s : (α × Fin 2) ⊕ α → K) : α × Fin 2 → K :=
  fun p => if p.1 ∈ V₁ then q₁ p else s (Sum.inl p)

open Classical in
/-- **The height of ear data** over the base heights `z₁`, at the picture `q`
(`lem:pencil-ear-data`): `z₁` on `V₁`, the plane `ha` at the first interior body `xf`, the plane
`hb` at the last `xl`, the free heights `m` at the other interior bodies `X`, and `0` elsewhere. -/
noncomputable def earHeight (q : α × Fin 2 → K) (m : α → K) : α → K :=
  fun w => if w ∈ V₁ then z₁ w else if w = xf then ha ⬝ᵥ pencilPicturePoint q w
    else if w = xl then hb ⬝ᵥ pencilPicturePoint q w else if w ∈ X then m w else 0

/-- **The configuration of ear data** (`lem:pencil-ear-data`), as the configuration point function
`PanelHingeFramework.ofNormals` reads: the points of `(earPicture s, earHeight … (s ∘ inr))`. -/
noncomputable def earConfig (s : (α × Fin 2) ⊕ α → K) : α × Fin 4 → K :=
  fun p => pencilConfigPoint (earPicture V₁ q₁ s)
    (earHeight V₁ z₁ xf xl X ha hb (earPicture V₁ q₁ s) (fun w => s (Sum.inr w))) p.1 p.2

open Classical in
/-- The picture coordinates of ear data, as polynomials in the ear data. -/
noncomputable def earPicturePoly (p : α × Fin 2) : MvPolynomial ((α × Fin 2) ⊕ α) K :=
  if p.1 ∈ V₁ then MvPolynomial.C (q₁ p) else MvPolynomial.X (Sum.inl p)

open Classical in
/-- The height coordinates of ear data, as polynomials in the ear data. -/
noncomputable def earHeightPoly (w : α) : MvPolynomial ((α × Fin 2) ⊕ α) K :=
  if w ∈ V₁ then MvPolynomial.C (z₁ w)
  else if w = xf then MvPolynomial.C (ha 0) * MvPolynomial.X (Sum.inl (w, 0))
    + MvPolynomial.C (ha 1) * MvPolynomial.X (Sum.inl (w, 1)) + MvPolynomial.C (ha 2)
  else if w = xl then MvPolynomial.C (hb 0) * MvPolynomial.X (Sum.inl (w, 0))
    + MvPolynomial.C (hb 1) * MvPolynomial.X (Sum.inl (w, 1)) + MvPolynomial.C (hb 2)
  else if w ∈ X then MvPolynomial.X (Sum.inr w) else 0

/-- The configuration points of ear data, as polynomials in the ear data. -/
noncomputable def earPointPoly (p : α × Fin 4) : MvPolynomial ((α × Fin 2) ⊕ α) K :=
  ![earPicturePoly V₁ q₁ (p.1, 0), earPicturePoly V₁ q₁ (p.1, 1),
    earHeightPoly V₁ z₁ xf xl X ha hb p.1, 1] p.2

theorem eval_earPicturePoly (s : (α × Fin 2) ⊕ α → K) (p : α × Fin 2) :
    MvPolynomial.eval s (earPicturePoly V₁ q₁ p) = earPicture V₁ q₁ s p := by
  unfold earPicturePoly earPicture
  split_ifs <;> simp

/-- **The configuration points of ear data are polynomial in the ear data**
(`lem:pencil-ear-data`(1)). -/
theorem eval_earPointPoly (s : (α × Fin 2) ⊕ α → K) (p : α × Fin 4) :
    MvPolynomial.eval s (earPointPoly V₁ q₁ z₁ xf xl X ha hb p) =
      earConfig V₁ q₁ z₁ xf xl X ha hb s p := by
  obtain ⟨w, j⟩ := p
  fin_cases j
  · simp [earPointPoly, earConfig, pencilConfigPoint, eval_earPicturePoly]
  · simp [earPointPoly, earConfig, pencilConfigPoint, eval_earPicturePoly]
  · simp only [earPointPoly, earConfig, pencilConfigPoint]
    simp only [Fin.reduceFinMk, Matrix.cons_val, earHeightPoly, earHeight]
    by_cases hw : w ∈ V₁
    · simp [hw]
    · by_cases hf : w = xf
      · subst hf
        simp [hw, dotProduct, Fin.sum_univ_three, pencilPicturePoint, earPicture]
      · by_cases hl : w = xl
        · subst hl
          simp [hw, hf, dotProduct, Fin.sum_univ_three, pencilPicturePoint, earPicture]
        · by_cases hX : w ∈ X <;> simp [hw, hf, hl, hX]
  · simp [earPointPoly, earConfig, pencilConfigPoint]

/-- **Pictures along the ear data** (`lem:pencil-ear-data`(2)): a polynomial in the picture
becomes a polynomial in the ear data. -/
theorem eval_bind₁_earPicturePoly (s : (α × Fin 2) ⊕ α → K) (P : MvPolynomial (α × Fin 2) K) :
    MvPolynomial.eval s (MvPolynomial.bind₁ (earPicturePoly V₁ q₁) P) =
      MvPolynomial.eval (earPicture V₁ q₁ s) P := by
  rw [MvPolynomial.eval_bind₁]
  exact congrArg (fun f => MvPolynomial.eval f P) (funext (eval_earPicturePoly V₁ q₁ s))

end EarData

section EarDataFacts

variable {V₁ : Set α} {q₁ : α × Fin 2 → K} {z₁ : α → K} {xf xl : α} {X : Set α}
  {la lb : Fin 3 → K}

omit [Field K] in
/-- On `V₁` the picture of ear data is the base picture. -/
theorem earPicture_of_mem (s : (α × Fin 2) ⊕ α → K) {w : α} (hw : w ∈ V₁) (i : Fin 2) :
    earPicture V₁ q₁ s (w, i) = q₁ (w, i) := by
  simp [earPicture, hw]

omit [Field K] in
/-- Off `V₁` the picture of ear data is its own coordinate. -/
theorem earPicture_of_notMem (s : (α × Fin 2) ⊕ α → K) {w : α} (hw : w ∉ V₁) (i : Fin 2) :
    earPicture V₁ q₁ s (w, i) = s (Sum.inl (w, i)) := by
  simp [earPicture, hw]

/-- **On `V₁` the configuration of ear data is the base configuration**
(`lem:pencil-ear-data`(1)). -/
theorem earConfig_of_mem (s : (α × Fin 2) ⊕ α → K) {w : α} (hw : w ∈ V₁) (i : Fin 4) :
    earConfig V₁ q₁ z₁ xf xl X la lb s (w, i) = pencilConfigPoint q₁ z₁ w i := by
  fin_cases i <;> simp [earConfig, pencilConfigPoint, earPicture, earHeight, hw]

/-- The configuration point of a middle body of the ear: its picture and free height. -/
theorem earConfig_of_mem_X (s : (α × Fin 2) ⊕ α → K) {w : α} (hw : w ∉ V₁) (hf : w ≠ xf)
    (hl : w ≠ xl) (hX : w ∈ X) :
    (fun i => earConfig V₁ q₁ z₁ xf xl X la lb s (w, i)) =
      ![s (Sum.inl (w, 0)), s (Sum.inl (w, 1)), s (Sum.inr w), 1] := by
  funext i
  fin_cases i <;> simp [earConfig, pencilConfigPoint, earPicture, earHeight, hw, hf, hl, hX]

/-- The configuration point of the first interior body lies on the plane `la`. -/
theorem earConfig_first (s : (α × Fin 2) ⊕ α → K) (hw : xf ∉ V₁) :
    (fun i => earConfig V₁ q₁ z₁ xf xl X la lb s (xf, i)) =
      liftPlane la ![s (Sum.inl (xf, 0)), s (Sum.inl (xf, 1)), 1] := by
  funext i
  fin_cases i <;> simp [earConfig, pencilConfigPoint, earPicture, earHeight, hw, liftPlane,
    pencilPicturePoint]

/-- The configuration point of the last interior body lies on the plane `lb`. -/
theorem earConfig_last (s : (α × Fin 2) ⊕ α → K) (hw : xl ∉ V₁) (hfl : xl ≠ xf) :
    (fun i => earConfig V₁ q₁ z₁ xf xl X la lb s (xl, i)) =
      liftPlane lb ![s (Sum.inl (xl, 0)), s (Sum.inl (xl, 1)), 1] := by
  funext i
  fin_cases i <;> simp [earConfig, pencilConfigPoint, earPicture, earHeight, hw, hfl, liftPlane,
    pencilPicturePoint]

end EarDataFacts

open Classical in
/-- **The heights of ear data are lifting heights** (`lem:pencil-ear-data`(1)): at a picture
admissible for `G`, the base heights `z₁ ∈ L_{G[V₁]}(q)`, continued by planes `la`, `lb` agreeing
with `z₁` on the closed neighbourhoods of `a`, `b` in `G[V₁]` to the first and last interior bodies
and freely in the middle, form a height of `G`. This is `Graph.earExtend_mem_liftingSpace` with
the planes and the free heights explicit; its proof is the same, through
`Graph.mem_liftingSpace_of_ear`. -/
theorem _root_.Graph.earHeight_mem_liftingSpace [Finite α] {G : Graph α β} {V₁ : Set α}
    {k : ℕ} {x : Fin k → α} {a b : α} {e : Fin (k + 1) → β} (hk : 2 ≤ k)
    (hcover : V(G) = V₁ ∪ Set.range x) (hinj : Function.Injective x) (hxV₁ : ∀ i, x i ∉ V₁)
    (ha : a ∈ V₁) (hb : b ∈ V₁) (hab : a ≠ b)
    (hpath : ∀ i : Fin (k + 1),
      G.IsLink (e i) (pathVertex a x b i.castSucc) (pathVertex a x b i.succ))
    (hsep : ∀ f u w, G.IsLink f u w → (∀ i, f ≠ e i) → u ∈ V₁ ∧ w ∈ V₁)
    {q : α × Fin 2 → K} (hq : G.IsAdmissiblePicture q) {z₁ : α → K}
    (hz₁ : z₁ ∈ (G.induce V₁).liftingSpace q) {la lb : Fin 3 → K}
    (hla : ∀ w ∈ (G.induce V₁).closedNbhd a, z₁ w = la ⬝ᵥ pencilPicturePoint q w)
    (hlb : ∀ w ∈ (G.induce V₁).closedNbhd b, z₁ w = lb ⬝ᵥ pencilPicturePoint q w) (m : α → K) :
    earHeight V₁ z₁ (x ⟨0, by omega⟩) (x ⟨k - 1, by omega⟩) (Set.range x) la lb q m
      ∈ G.liftingSpace q := by
  have hx0l : x ⟨0, by omega⟩ ≠ x ⟨k - 1, by omega⟩ := fun h => by
    have := hinj h; simp [Fin.ext_iff] at this; omega
  set z := earHeight V₁ z₁ (x ⟨0, by omega⟩) (x ⟨k - 1, by omega⟩) (Set.range x) la lb q m
    with hzdef
  have hzV₁ : ∀ w ∈ V₁, z w = z₁ w := fun w hw => by simp [hzdef, earHeight, hw]
  have hz0 : z (x ⟨0, by omega⟩) = la ⬝ᵥ pencilPicturePoint q (x ⟨0, by omega⟩) := by
    simp [hzdef, earHeight, hxV₁]
  have hzl : z (x ⟨k - 1, by omega⟩) = lb ⬝ᵥ pencilPicturePoint q (x ⟨k - 1, by omega⟩) := by
    simp [hzdef, earHeight, hxV₁, hx0l.symm]
  refine G.mem_liftingSpace_of_ear hcover hinj hxV₁ ha hb hpath hsep hq (fun w hw => ?_)
    (fun v hv => ?_)
  · rw [hcover] at hw
    simp only [Set.mem_union, not_or] at hw
    have h0 : w ≠ x ⟨0, by omega⟩ := fun h => hw.2 ⟨_, h.symm⟩
    have hl : w ≠ x ⟨k - 1, by omega⟩ := fun h => hw.2 ⟨_, h.symm⟩
    simp [hzdef, earHeight, hw.1, h0, hl, hw.2]
  · by_cases hva : v = a
    · subst hva
      refine ⟨la, fun w hw => ?_⟩
      rcases G.mem_closedNbhd_induce_of_ear (by omega) hxV₁ ha hb hpath hsep hv hw with
        hw' | ⟨-, rfl⟩ | ⟨h, rfl⟩
      · rw [hzV₁ w (Graph.closedNbhd_subset_vertexSet hv hw')]; exact hla w hw'
      · exact hz0
      · exact absurd h hab
    · by_cases hvb : v = b
      · subst hvb
        refine ⟨lb, fun w hw => ?_⟩
        rcases G.mem_closedNbhd_induce_of_ear (by omega) hxV₁ ha hb hpath hsep hv hw with
          hw' | ⟨h, -⟩ | ⟨-, rfl⟩
        · rw [hzV₁ w (Graph.closedNbhd_subset_vertexSet hv hw')]; exact hlb w hw'
        · exact absurd h hva
        · exact hzl
      · obtain ⟨h, hh⟩ := hz₁.2 v hv
        refine ⟨h, fun w hw => ?_⟩
        rcases G.mem_closedNbhd_induce_of_ear (by omega) hxV₁ ha hb hpath hsep hv hw with
          hw' | ⟨h', -⟩ | ⟨h', -⟩
        · rw [hzV₁ w (Graph.closedNbhd_subset_vertexSet hv hw')]; exact hh w hw'
        · exact absurd h' hva
        · exact absurd h' hvb

/-! ## Openness along a polynomial parametrization of the configuration points

`P : α × Fin 4 → MvPolynomial σ K` gives the point of body `w` at the parameter `s` as
`fun j => eval s (P (w, j))`. Each bound below is the non-vanishing of one polynomial in `s`,
nonzero at a given witness (`lem:pencil-ear-data`(3)). -/

section Transfer

variable {σ : Type*}

/-- **A rank lower bound is open along the parametrization** (`lem:pencil-ear-data`(3), the rank
half): the rank polynomial of `PanelHingeFramework.exists_rankPolynomial_of_le_finrank_linking`,
substituted. The witness must have nonzero hinges at the links of `H`. -/
theorem exists_mvPolynomial_le_finrank_ofNormals_bind [Finite α] [Finite β]
    (H : Graph α β) (ends : β → α × α)
    (hends : ∀ e u v, H.IsLink e u v → H.IsLink e (ends e).1 (ends e).2)
    (P : α × Fin 4 → MvPolynomial σ K) {s₀ : σ → K}
    (hne : ∀ e, H.IsLink e (ends e).1 (ends e).2 →
      (PanelHingeFramework.ofNormals (k := 2) H ends
        (fun p => MvPolynomial.eval s₀ (P p))).toBodyHinge.supportExtensor e ≠ 0)
    {N : ℕ} (hN : N ≤ Module.finrank K (Submodule.span K
      (PanelHingeFramework.ofNormals (k := 2) H ends
        (fun p => MvPolynomial.eval s₀ (P p))).toBodyHinge.rigidityRows)) :
    ∃ Q : MvPolynomial σ K, MvPolynomial.eval s₀ Q ≠ 0 ∧ ∀ s, MvPolynomial.eval s Q ≠ 0 →
      N ≤ Module.finrank K (Submodule.span K
        (PanelHingeFramework.ofNormals (k := 2) H ends
          (fun p => MvPolynomial.eval s (P p))).toBodyHinge.rigidityRows) := by
  obtain ⟨Q, hQ₀, hQ⟩ :=
    PanelHingeFramework.exists_rankPolynomial_of_le_finrank_linking H ends hends hne hN
  refine ⟨MvPolynomial.bind₁ P Q, by rwa [MvPolynomial.eval_bind₁], fun s hs => hQ _ ?_⟩
  rwa [MvPolynomial.eval_bind₁] at hs

/-- The flat coordinates of the join of two polynomial points (`lem:pencil-join-flat`). -/
noncomputable def joinPoly (A B : Fin 4 → MvPolynomial σ K) :
    Fin 3 ⊕ Fin 3 → MvPolynomial σ K
  | Sum.inl j => A 2 * ![B 0, B 1, B 3] j - B 2 * ![A 0, A 1, A 3] j
  | Sum.inr j => crossProduct ![A 0, A 1, A 3] ![B 0, B 1, B 3] j

theorem eval_joinPoly (A B : Fin 4 → MvPolynomial σ K) (s : σ → K) (t : Fin 3 ⊕ Fin 3) :
    MvPolynomial.eval s (joinPoly A B t) = flatCoords (pointJoin
      (fun j => MvPolynomial.eval s (A j)) (fun j => MvPolynomial.eval s (B j))) t := by
  rcases t with j | j
  · rw [flatCoords_pointJoin_inl]
    fin_cases j <;> simp [joinPoly, planarProj_apply]
  · rw [flatCoords_pointJoin_inr, joinPoly, eval_crossProduct, planarProj_apply,
      planarProj_apply]
    congr 2

/-- **A span lower bound is open along the parametrization** (`lem:pencil-ear-data`(3), the family
half): for a fixed subspace `ρ` and any family of joins of configuration points,
`N ≤ dim(ρ ⊔ span joins)` at `s₀` persists off the zero set of a polynomial nonzero at `s₀`. A
basis of `ρ` together with the joins has polynomial flat coordinates (`eval_joinPoly`), and `N` of
them independent at `s₀` stay independent off a maximal minor
(`exists_polynomial_ne_zero_of_linearIndependent_at_reindex`). No admissibility and no nonzero
hinge is asked of the witness. -/
theorem exists_mvPolynomial_le_finrank_sup_span_pointJoin {ι : Type*}
    (ρ : Submodule K (ScrewSpace K 2)) (P : α × Fin 4 → MvPolynomial σ K) (u w : ι → α)
    {s₀ : σ → K} {N : ℕ}
    (hN : N ≤ Module.finrank K ↥(ρ ⊔ Submodule.span K (Set.range fun i =>
      pointJoin (fun j => MvPolynomial.eval s₀ (P (u i, j)))
        (fun j => MvPolynomial.eval s₀ (P (w i, j)))))) :
    ∃ Q : MvPolynomial σ K, MvPolynomial.eval s₀ Q ≠ 0 ∧ ∀ s, MvPolynomial.eval s Q ≠ 0 →
      N ≤ Module.finrank K ↥(ρ ⊔ Submodule.span K (Set.range fun i =>
        pointJoin (fun j => MvPolynomial.eval s (P (u i, j)))
          (fun j => MvPolynomial.eval s (P (w i, j))))) := by
  classical
  set b := Module.finBasis K ρ with hb
  set g : (σ → K) → Fin (Module.finrank K ρ) ⊕ ι → ScrewSpace K 2 := fun s =>
    Sum.elim (fun i => (b i : ScrewSpace K 2)) (fun i =>
      pointJoin (fun j => MvPolynomial.eval s (P (u i, j)))
        (fun j => MvPolynomial.eval s (P (w i, j)))) with hg
  have hspan : ∀ s, Submodule.span K (Set.range (g s)) = ρ ⊔ Submodule.span K (Set.range fun i =>
      pointJoin (fun j => MvPolynomial.eval s (P (u i, j)))
        (fun j => MvPolynomial.eval s (P (w i, j)))) := by
    intro s
    rw [hg, Set.Sum.elim_range, Submodule.span_union]
    congr 1
    have := congrArg (Submodule.map ρ.subtype) b.span_eq
    rw [Submodule.map_span, Submodule.map_subtype_top, ← Set.range_comp] at this
    exact this
  set c : Fin (Module.finrank K ρ) ⊕ ι → Fin 3 ⊕ Fin 3 → MvPolynomial σ K :=
    Sum.elim (fun i t => MvPolynomial.C (flatCoords (b i : ScrewSpace K 2) t))
      (fun i => joinPoly (fun j => P (u i, j)) (fun j => P (w i, j))) with hc
  have hgc : ∀ s i t, flatCoords (g s i) t = MvPolynomial.eval s (c i t) := by
    intro s i t
    rcases i with i | i
    · simp [hg, hc]
    · simp only [hg, hc, Sum.elim_inr]
      rw [eval_joinPoly]
  -- `N` independent members of the family at `s₀`
  have hN' : N ≤ Module.finrank K (Submodule.span K (Set.range (g s₀))) := by
    rw [hspan]; exact hN
  obtain ⟨f, hfmem, -, hfli⟩ := Submodule.exists_fun_fin_finrank_span_eq K (Set.range (g s₀))
  choose idx hidx using hfmem
  set j : Fin N → Fin (Module.finrank K ρ) ⊕ ι := fun i => idx (Fin.castLE hN' i) with hj
  have hjinj : Function.Injective j := by
    intro a a' h
    have : f (Fin.castLE hN' a) = f (Fin.castLE hN' a') := by
      rw [← hidx, ← hidx]; exact congrArg (g s₀) h
    exact Fin.castLE_injective hN' (hfli.injective this)
  have hli₀ : LinearIndependent K (fun i : (Set.univ : Set (Fin N)) => g s₀ (j i)) := by
    have : (fun i : (Set.univ : Set (Fin N)) => g s₀ (j i)) =
        f ∘ Fin.castLE hN' ∘ Subtype.val := by
      funext i; simp [hj, hidx]
    rw [this]
    exact (hfli.comp _ (Fin.castLE_injective hN')).comp _ Subtype.val_injective
  set e : Fin (Module.finrank K (ScrewSpace K 2)) ≃ (Fin 3 ⊕ Fin 3) :=
    (finCongr finrank_screwSpace_two).trans finSumFinEquiv.symm with he
  obtain ⟨Q, hQ₀, hQ⟩ := exists_polynomial_ne_zero_of_linearIndependent_at_reindex
    (W := ScrewSpace K 2) e (fun s i => g s (j i)) (fun i => c (j i)) flatCoords
    (fun s i t => hgc s (j i) t) hli₀
  refine ⟨Q, hQ₀, fun s hs => ?_⟩
  have hli := (hQ s hs).comp (fun i => (⟨i, trivial⟩ : (Set.univ : Set (Fin N))))
    (fun _ _ h => congrArg Subtype.val h)
  rw [← hspan]
  calc N = Fintype.card (Fin N) := (Fintype.card_fin N).symm
    _ = Module.finrank K (Submodule.span K (Set.range (fun i => g s (j i)))) :=
        (finrank_span_eq_card hli).symm
    _ ≤ _ := Submodule.finrank_mono (Submodule.span_mono (by
        rintro _ ⟨i, rfl⟩; exact ⟨_, rfl⟩))

end Transfer

end CombinatorialRigidity.Molecular
