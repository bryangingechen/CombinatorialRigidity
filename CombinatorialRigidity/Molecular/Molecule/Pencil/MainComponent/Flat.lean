/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.Molecule.Pencil.MainComponent.Configuration

/-!
# The flat rank (Phase 40c FLAT)

The rank of a *flat* configuration `(q, 0)` over an admissible planar picture `q`
(`blueprint/src/chapter/main-component.tex`, `sec:main-component-flat`; informal Step MC4/MC5 of
§(K-main), `notes/Phase40c.md`). Every hinge `p_u ∧ p_v` of a flat configuration lies in the plane
`z = 0`, so the screw space splits as `Λ²K⁴ = W′ ⊕ W_Π` (`flatScrewEquiv`): the `W′` part is glued
across every edge (constant on a connected graph), and the `W_Π` part's motions are the
**lifting planes** `F(q)`, the families of affine functions `h_v` on `K²` that agree at both ends of
every edge. Evaluating `h_w` at `q_w` maps `F(q)` onto the lifting space `L(q)`, so the flat rank
is exactly `6|V| − 3 − dim L(q)` ((MC-4)(a)). `F(q)` is also the motion space of the plane
panel-hinge framework at the normals `(x_v, y_v, 1)`, whose partition bound gives
`dim L(q) ≥ 3 + def₂` ((MC-4)(b)). With `def₃ ≤ def₂` on a connected graph
(`Graph.Connected.deficiency_three_le_deficiency_two`, (MC-5)(i)), an admissible picture with
`dim L(q) ≤ 3 + def₃` is main and its flat configuration attains, so `X₀` attains ((MC-5)(ii),
(iii)). The joins of two points in these coordinates, and the Zariski-openness of their
independence, serve the ear steps (Phase 40g CHAIN, `sec:main-component-chain`).

## Main definitions

* `Graph.liftingPlanes` — the lifting planes `F(q)`, free off `V(G)` like every motion space.
* `screwOneEquiv` — the grade-1 screw space `ScrewSpace K 1 ≃ K³`.
* `flatScrewEquiv` — the flat split `ScrewSpace K 2 ≃ K³ × K³`, `S ↦ (σ S, π S)`.
* `Graph.linkConstants` — the families `α → K³` equal across every link (the glued block).
* `pointJoin` — the join `p ∧ p'` of two points of `K⁴`, as a screw; `flatCoords` — the flat
  coordinates on `Fin 3 ⊕ Fin 3`; `joinPicturePoly`, `joinHeightPoly` — a join's flat coordinates
  as polynomials in the picture and in the heights (Phase 40g).

## Main statements

* `Graph.finrank_liftingPlanes` — `dim F(q) = 3|V(G)ᶜ| + dim L(q)` at an admissible picture.
* `Graph.finrank_infinitesimalMotions_ofNormals_pencilPicturePoint` — `F(q)` is the grade-1
  motion space at the normals `(x_v, y_v, 1)`;
  `Graph.finrank_span_rigidityRows_ofNormals_pencilPicturePoint` is its rank form
  `3|V(G)| − dim L(q)`.
* `Graph.three_add_deficiency_le_finrank_liftingSpace` — (MC-4)(b), `3 + def₂ ≤ dim L(q)`.
* `Graph.finrank_infinitesimalMotions_pointJoinFramework_flat` — the flat motion space has
  dimension `3(|V(G)ᶜ| + 1) + dim F(q)` on a connected graph.
* `Graph.finrank_span_rigidityRows_ofNormals_flat` — (MC-4)(a), the flat rank
  `6|V(G)| − 3 − dim L(q)`, at the rank `Graph.X0Attains` reads; `_flat_le` and `_flat_eq_iff`
  give (MC-4)(c).
* `Graph.x0Attains_of_finrank_liftingSpace_le` — `X₀` attains at the flat witness when
  `dim L(q) ≤ 3 + def₃`; `Graph.x0Attains_of_finrank_liftingSpace_eq_three` is (MC-5)(iii).
* `flatScrewEquiv_pointJoin`, `linearIndependent_pointJoin_of_flat` — a join is
  `(p_z p̄′ − p′_z p̄, p̄ × p̄′)` in flat coordinates, and independence of joins is read there
  (`lem:pencil-join-flat`, Phase 40g); `flatSigma_pointJoin` and `flatPi_pointJoin` are its two
  components, and `pointJoin_swap`, `pointJoin_self`, `pointJoin_add_smul_left` say the join is
  alternating and linear in its first point, and `pointJoin_add_smul_self_right` that it is
  unchanged by moving its second point along the first (Phase 40h, for `MainComponent/Lines.lean`);
  `pointJoin_{zero,add,smul,sub}_left` and `pointJoin_{add,smul,sub}_right` restate the linearity
  as a plain (not affine) bilinear map (Phase 40i ORBIT).
* `linearIndependent_pencilConfigPoint_triple` — three configuration points over independent
  picture points are independent, for any heights (Phase 40i ORBIT).
* `exists_mvPolynomial_linearIndependent_pointJoin_picture`,
  `exists_mvPolynomial_linearIndependent_pointJoin_heights` — independence of joins is
  Zariski-open in the picture and in the heights (`lem:pencil-join-independence-open`).

## Design

* **The flat (primal) side.** The rank is computed on the point-join framework at `z = 0` and
  carried to the `ofNormals` framework `Graph.X0Attains` reads by the polarity
  (`ofNormals_toBodyHinge_eq_mapSupport_pointJoinFramework`,
  `BodyHingeFramework.finrank_span_rigidityRows_mapSupport`).
* **Coordinates on the opaque screw space** come from alternating forms lifted along
  `exteriorPower.alternatingMapLinearEquiv` (the `Molecule/ScrewVelocity.lean` pattern, over every
  field), so no basis of `ScrewSpace K 2` is chosen; `flatScrewEquiv` is bijective by an explicit
  right inverse and `6 = 6`.
* **Motion spaces are compared by linear equivalences** (`LinearEquiv.ofBijective`), so (MC-4)(a)
  is an identity, not a pair of inequalities.
-/

open scoped Matrix
open scoped Graph

namespace CombinatorialRigidity.Molecular

variable {K : Type*} [Field K]
variable {α β : Type*}

/-! ## The lifting planes `F(q)` -/

/-- **A vector lies on the line spanned by `a ×₃ b` iff it is orthogonal to `a` and `b`**, for
independent `a, b ∈ K³` (Phase 40c FLAT). The forward direction is `a ⬝ (a ×₃ b) = 0`; the reverse
is `(a ×₃ b) ×₃ x = (a ⬝ x) b − (b ⬝ x) a = 0` with `a ×₃ b ≠ 0`. -/
theorem mem_span_crossProduct_iff {a b x : Fin 3 → K} (hab : LinearIndependent K ![a, b]) :
    x ∈ Submodule.span K {crossProduct a b} ↔ x ⬝ᵥ a = 0 ∧ x ⬝ᵥ b = 0 := by
  constructor
  · intro hx
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hx
    rw [smul_dotProduct, smul_dotProduct, dotProduct_comm, dot_self_cross, dotProduct_comm,
      dot_cross_self, smul_zero]
    exact ⟨rfl, rfl⟩
  · rintro ⟨ha, hb⟩
    have hc : crossProduct a b ≠ 0 := crossProduct_ne_zero_iff_linearIndependent.mpr hab
    have hdep : ¬ LinearIndependent K ![crossProduct a b, x] := by
      rw [← crossProduct_ne_zero_iff_linearIndependent, not_not, cross_cross_eq_smul_sub_smul,
        dotProduct_comm a x, dotProduct_comm b x, ha, hb, zero_smul, zero_smul, sub_zero]
    rw [LinearIndependent.pair_iff' hc] at hdep
    push Not at hdep
    obtain ⟨t, ht⟩ := hdep
    exact Submodule.mem_span_singleton.mpr ⟨t, ht⟩

/-- **The lifting planes `F(q)`** (`def:pencil-lifting-planes`; Phase 40c FLAT, informal (MC-4)'s
`F(q)`): families `h : α → K³`, each `h_v` read as the affine function `(x, y) ↦ h_v ⬝ (x, y, 1)`,
whose difference across every link vanishes at both ends' picture points. Families are
unconstrained off `V(G)`, like every motion space, so a body off `V(G)` adds `3` to the dimension
(`Graph.finrank_liftingPlanes`). -/
def _root_.Graph.liftingPlanes (G : Graph α β) (q : α × Fin 2 → K) :
    Submodule K (α → Fin 3 → K) where
  carrier := {h | ∀ e u v, G.IsLink e u v →
    (h u - h v) ⬝ᵥ pencilPicturePoint q u = 0 ∧ (h u - h v) ⬝ᵥ pencilPicturePoint q v = 0}
  zero_mem' := fun _ _ _ _ => by simp
  add_mem' := by
    rintro h₁ h₂ hh₁ hh₂ e u v he
    obtain ⟨a₁, b₁⟩ := hh₁ e u v he
    obtain ⟨a₂, b₂⟩ := hh₂ e u v he
    simp only [Pi.add_apply, add_sub_add_comm, add_dotProduct, a₁, a₂, b₁, b₂, add_zero, and_self]
  smul_mem' := by
    rintro c h hh e u v he
    obtain ⟨a, b⟩ := hh e u v he
    simp only [Pi.smul_apply, ← smul_sub, smul_dotProduct, a, b, smul_zero, and_self]

open Classical in
/-- **The evaluation `Φ`** (`lem:pencil-lifting-planes-dim`; informal (MC-4)): a family `h` goes to
the height `w ↦ h_w(q_w)` on `V(G)`, zero off `V(G)`. -/
noncomputable def _root_.Graph.liftingPlanesEval (G : Graph α β) (q : α × Fin 2 → K) :
    (α → Fin 3 → K) →ₗ[K] (α → K) where
  toFun h w := if w ∈ V(G) then h w ⬝ᵥ pencilPicturePoint q w else 0
  map_add' h₁ h₂ := by funext w; by_cases hw : w ∈ V(G) <;> simp [hw, add_dotProduct]
  map_smul' c h := by funext w; by_cases hw : w ∈ V(G) <;> simp [hw, smul_dotProduct]

/-- **`Φ` maps the lifting planes into the lifting space** (`lem:pencil-lifting-planes-dim`): for a
neighbour `w` of `v`, `h_w(q_w) = h_v(q_w)`, so `Φ h` restricts on the closed neighbourhood of `v`
to the affine function `h_v`. -/
theorem _root_.Graph.liftingPlanesEval_mem_liftingSpace {G : Graph α β} {q : α × Fin 2 → K}
    {h : α → Fin 3 → K} (hh : h ∈ G.liftingPlanes q) :
    G.liftingPlanesEval q h ∈ G.liftingSpace q := by
  classical
  refine ⟨fun w hw => by simp [Graph.liftingPlanesEval, hw], fun v hv => ⟨h v, fun w hw => ?_⟩⟩
  rcases hw with rfl | ⟨e, he⟩
  · simp [Graph.liftingPlanesEval, hv]
  · have := (hh e w v he.symm).1
    rw [sub_dotProduct, sub_eq_zero] at this
    simpa [Graph.liftingPlanesEval, he.right_mem] using this

/-- **`dim F(q) = 3|V(G)ᶜ| + dim L(q)` at an admissible picture** (`lem:pencil-lifting-planes-dim`;
informal (MC-4)'s bijection `F(q) ≅ L(q)`, with the free bodies off `V(G)` counted). `Φ` maps
`F(q)` onto `L(q)`: for `z ∈ L(q)` the per-body interpolants form a family in `F(q)`, since both
ends of a link lie in both closed neighbourhoods. Its kernel is the families vanishing on `V(G)`:
at a body `v`, `h_v` vanishes at the three non-collinear picture points admissibility provides.
Rank–nullity finishes. -/
theorem _root_.Graph.finrank_liftingPlanes [Finite α] {G : Graph α β} {q : α × Fin 2 → K}
    (hq : G.IsAdmissiblePicture q) :
    Module.finrank K (G.liftingPlanes q) =
      3 * V(G)ᶜ.ncard + Module.finrank K (G.liftingSpace q) := by
  classical
  have : Fintype α := Fintype.ofFinite α
  set T := (G.liftingPlanesEval q).domRestrict (G.liftingPlanes q) with hT
  -- the range of `Φ` on `F(q)` is `L(q)`
  have hrange : LinearMap.range T = G.liftingSpace q := by
    refine le_antisymm ?_ fun z hz => ?_
    · rintro _ ⟨⟨h, hh⟩, rfl⟩
      exact G.liftingPlanesEval_mem_liftingSpace hh
    obtain ⟨hs, ha⟩ := hz
    choose! c hc using ha
    refine ⟨⟨fun v => if v ∈ V(G) then c v else 0, fun e u v he => ?_⟩, ?_⟩
    · simp only [he.left_mem, he.right_mem, ↓reduceIte, sub_dotProduct]
      rw [← hc u he.left_mem u (Or.inl rfl), ← hc v he.right_mem u (Or.inr ⟨e, he.symm⟩),
        ← hc u he.left_mem v (Or.inr ⟨e, he⟩), ← hc v he.right_mem v (Or.inl rfl), sub_self,
        sub_self]
      exact ⟨rfl, rfl⟩
    · funext w
      by_cases hw : w ∈ V(G)
      · simp [hT, Graph.liftingPlanesEval, hw, ← hc w hw w (Or.inl rfl)]
      · simp [hT, Graph.liftingPlanesEval, hw, hs w hw]
  -- the kernel is the families vanishing on `V(G)`, of dimension `3|V(G)ᶜ|`
  set W : Submodule K (α → Fin 3 → K) :=
    LinearMap.ker (LinearMap.funLeft K (Fin 3 → K) (Subtype.val : V(G) → α)) with hW
  have hker : (LinearMap.ker T).map (G.liftingPlanes q).subtype = W := by
    ext h
    simp only [Submodule.mem_map, LinearMap.mem_ker, hW, Submodule.subtype_apply]
    constructor
    · rintro ⟨⟨h, hh⟩, hT0, rfl⟩
      funext ⟨v, hv⟩
      obtain ⟨t, ht, hli⟩ := hq.2 v hv
      -- `h_v` vanishes at the three picture points of the admissible triple at `v`
      have hperp : ∀ i, h v ⬝ᵥ pencilPicturePoint q (t i) = 0 := by
        intro i
        have htV : t i ∈ V(G) := by
          rcases ht i with h' | ⟨e, he⟩
          · exact h' ▸ hv
          · exact he.right_mem
        have h0 : h (t i) ⬝ᵥ pencilPicturePoint q (t i) = 0 := by
          simpa [hT, Graph.liftingPlanesEval, htV] using congr_fun hT0 (t i)
        rcases ht i with h' | ⟨e, he⟩
        · rwa [h'] at h0 ⊢
        · have := (hh e v (t i) he).2
          rwa [sub_dotProduct, h0, sub_zero] at this
      have hunit : IsUnit (Matrix.of fun i => pencilPicturePoint q (t i)) :=
        Matrix.linearIndependent_rows_iff_isUnit.mp hli
      have hzero : (Matrix.of fun i => pencilPicturePoint q (t i)) *ᵥ h v =
          (Matrix.of fun i => pencilPicturePoint q (t i)) *ᵥ 0 := by
        rw [Matrix.mulVec_zero]
        funext i
        simp only [Matrix.mulVec, Matrix.of_apply, Pi.zero_apply]
        rw [dotProduct_comm]; exact hperp i
      exact Matrix.mulVec_injective_iff_isUnit.mpr hunit hzero
    · intro h0
      have hvan : ∀ v ∈ V(G), h v = 0 := fun v hv => congr_fun h0 ⟨v, hv⟩
      refine ⟨⟨h, fun e u v he => ?_⟩, ?_, rfl⟩
      · simp [hvan u he.left_mem, hvan v he.right_mem]
      · funext w
        by_cases hw : w ∈ V(G)
        · simp [hT, Graph.liftingPlanesEval, hw, hvan w hw]
        · simp [hT, Graph.liftingPlanesEval, hw]
  have hkerdim : Module.finrank K (LinearMap.ker T) = 3 * V(G)ᶜ.ncard := by
    rw [← Submodule.finrank_map_subtype_eq, hker]
    have hrn := LinearMap.finrank_range_add_finrank_ker
      (LinearMap.funLeft K (Fin 3 → K) (Subtype.val : V(G) → α))
    rw [LinearMap.range_eq_top.mpr (LinearMap.funLeft_surjective_of_injective K (Fin 3 → K)
      (Subtype.val : V(G) → α) Subtype.val_injective), finrank_top] at hrn
    have h1 : Module.finrank K (↥V(G) → Fin 3 → K) = V(G).ncard * 3 := by
      rw [Module.finrank_pi_fintype]; simp [Set.ncard_eq_toFinset_card']
    have h2 : Module.finrank K (α → Fin 3 → K) = Fintype.card α * 3 := by
      rw [Module.finrank_pi_fintype]; simp
    rw [h1, h2, ← Nat.card_eq_fintype_card,
      ← Set.ncard_add_ncard_compl V(G) (Set.toFinite _) (Set.toFinite _)] at hrn
    linarith
  have := LinearMap.finrank_range_add_finrank_ker T
  rw [hrange, hkerdim] at this
  omega

/-! ## Grade 1: the lifting planes are the motions of a plane framework -/

/-- **The grade-1 screw space is `K³`** (Phase 40c FLAT): `ScrewSpace K 1 = ⋀¹K³ ≃ K³`, through
the boundary equivalence and `exteriorPower.oneEquiv`. -/
noncomputable def screwOneEquiv : ScrewSpace K 1 ≃ₗ[K] (Fin 3 → K) :=
  (ScrewSpace.equivExteriorPower K 1).trans (exteriorPower.oneEquiv K (Fin 3 → K))

/-- `screwOneEquiv` reads a one-point extensor as its point. -/
theorem screwOneEquiv_mk_extensor (p : Fin 1 → Fin 3 → K) :
    screwOneEquiv (ScrewSpace.mk (extensor p) (extensor_mem_exteriorPower p)) = p 0 := by
  have h : ScrewSpace.equivExteriorPower K 1 (ScrewSpace.mk (extensor p)
      (extensor_mem_exteriorPower p)) = exteriorPower.ιMulti K 1 p := by
    apply Subtype.ext
    simp only [ScrewSpace.mk, ScrewSpace_def]
    rfl
  rw [screwOneEquiv, LinearEquiv.trans_apply, h, exteriorPower.oneEquiv_ιMulti]

/-- **The grade-1 hinge condition in `K³` coordinates** (`lem:pencil-lifting-planes-motions`):
for independent normals `n₁, n₂`, a screw lies on the span of their meet exactly when its
coordinate vector is orthogonal to both. The meet is a one-point extensor at a common
perpendicular (`exists_extensor_eq_panelSupportExtensor_gen`), nonzero, hence a nonzero multiple
of `n₁ ×₃ n₂` (`mem_span_crossProduct_iff`). -/
theorem mem_span_panelSupportExtensor_one_iff {n₁ n₂ : Fin 3 → K}
    (hn : LinearIndependent K ![n₁, n₂]) (D : ScrewSpace K 1) :
    D ∈ Submodule.span K {panelSupportExtensor (k := 1) n₁ n₂} ↔
      screwOneEquiv D ⬝ᵥ n₁ = 0 ∧ screwOneEquiv D ⬝ᵥ n₂ = 0 := by
  obtain ⟨p, hp, hperp⟩ := exists_extensor_eq_panelSupportExtensor_gen (k := 1) hn
  have hτC : screwOneEquiv (panelSupportExtensor (k := 1) n₁ n₂) = p 0 := by
    rw [show panelSupportExtensor (k := 1) n₁ n₂ =
        ScrewSpace.mk (extensor p) (extensor_mem_exteriorPower p) from ScrewSpace.ext hp,
      screwOneEquiv_mk_extensor]
  have hne : p 0 ≠ 0 := by
    rw [← hτC]
    exact (LinearEquiv.map_ne_zero_iff _).mpr ((panelSupportExtensor_ne_zero_iff _ _).mpr hn)
  obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.mp ((mem_span_crossProduct_iff hn).mpr (hperp 0))
  have hs0 : s ≠ 0 := by rintro rfl; rw [zero_smul] at hs; exact hne hs.symm
  rw [← mem_span_crossProduct_iff hn]
  constructor
  · intro hD
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hD
    rw [map_smul, hτC, ← hs, smul_smul]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · intro hD
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hD
    refine Submodule.mem_span_singleton.mpr ⟨t * s⁻¹, screwOneEquiv.injective ?_⟩
    rw [map_smul, hτC, ← hs, smul_smul, mul_assoc, inv_mul_cancel₀ hs0, mul_one, ht]

/-- **The lifting planes are the motions of the plane framework at the normals `(x_v, y_v, 1)`**
(`lem:pencil-lifting-planes-motions`; Phase 40c FLAT, the first bullet of BRIDGE). The pointwise
coordinate map `screwOneEquiv` is a linear equivalence between the motion space of the grade-1
panel-hinge framework with normals `(x_v, y_v, 1)` and `F(q)`, by
`mem_span_panelSupportExtensor_one_iff` at each link (adjacent picture points are independent,
`linearIndependent_pencilPicturePoint_pair`). -/
theorem _root_.Graph.finrank_infinitesimalMotions_ofNormals_pencilPicturePoint
    {G : Graph α β} {q : α × Fin 2 → K} (hq : G.IsAdmissiblePicture q) {ends : β → α × α}
    (hends : ∀ e u v, G.IsLink e u v → G.IsLink e (ends e).1 (ends e).2) :
    Module.finrank K (PanelHingeFramework.ofNormals (k := 1) G ends
      (fun p => pencilPicturePoint q p.1 p.2)).toBodyHinge.infinitesimalMotions
      = Module.finrank K (G.liftingPlanes q) := by
  set F := (PanelHingeFramework.ofNormals (k := 1) G ends
      (fun p => pencilPicturePoint q p.1 p.2)).toBodyHinge
  have hlink : ∀ (S : α → ScrewSpace K 1) e u v, G.IsLink e u v →
      (S u - S v ∈ Submodule.span K {F.supportExtensor e} ↔
        (screwOneEquiv (S u) - screwOneEquiv (S v)) ⬝ᵥ pencilPicturePoint q u = 0 ∧
        (screwOneEquiv (S u) - screwOneEquiv (S v)) ⬝ᵥ pencilPicturePoint q v = 0) := by
    intro S e u v he
    change S u - S v ∈ Submodule.span K {panelSupportExtensor (k := 1)
      (pencilPicturePoint q (ends e).1) (pencilPicturePoint q (ends e).2)} ↔ _
    rcases (hends e u v he).eq_and_eq_or_eq_and_eq he with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2, mem_span_panelSupportExtensor_one_iff
        (linearIndependent_pencilPicturePoint_pair (hq.1 e u v he)), map_sub]
    · rw [h1, h2, mem_span_panelSupportExtensor_one_iff
        (linearIndependent_pencilPicturePoint_pair (hq.1 e v u he.symm)), map_sub]
      exact and_comm
  let Φ : F.infinitesimalMotions →ₗ[K] G.liftingPlanes q :=
    { toFun := fun S => ⟨fun w => screwOneEquiv (S.1 w), fun e u v he =>
        (hlink S.1 e u v he).mp (S.2 e u v he)⟩
      map_add' := fun S T => by ext w i; simp
      map_smul' := fun c S => by ext w i; simp }
  refine (LinearEquiv.ofBijective Φ ⟨fun S T hST => Subtype.ext (funext fun w =>
    screwOneEquiv.injective (congr_arg (fun x : G.liftingPlanes q => x.1 w) hST)),
    fun h => ⟨⟨fun w => screwOneEquiv.symm (h.1 w), fun e u v he =>
      (hlink (fun w => screwOneEquiv.symm (h.1 w)) e u v he).mpr
        (by simpa using h.2 e u v he)⟩, ?_⟩⟩).finrank_eq
  ext w i; simp [Φ]

/-- **The grade-1 rank at the normals `(x_v, y_v, 1)` is `3|V(G)| − dim L(q)`**
(`lem:pencil-lifting-planes-motions`; the rank form BRIDGE consumes): the motion space is `F(q)`
(`Graph.finrank_infinitesimalMotions_ofNormals_pencilPicturePoint`), of dimension
`3|V(G)ᶜ| + dim L(q)` (`Graph.finrank_liftingPlanes`), inside the `3|α|`-dimensional screw
assignments. -/
theorem _root_.Graph.finrank_span_rigidityRows_ofNormals_pencilPicturePoint [Finite α]
    {G : Graph α β} {q : α × Fin 2 → K} (hq : G.IsAdmissiblePicture q) {ends : β → α × α}
    (hends : ∀ e u v, G.IsLink e u v → G.IsLink e (ends e).1 (ends e).2) :
    (Module.finrank K (Submodule.span K (PanelHingeFramework.ofNormals (k := 1) G ends
        (fun p => pencilPicturePoint q p.1 p.2)).toBodyHinge.rigidityRows) : ℤ)
      = 3 * (V(G).ncard : ℤ) - Module.finrank K (G.liftingSpace q) := by
  have hc := BodyHingeFramework.finrank_span_rigidityRows_add_finrank_infinitesimalMotions
    (PanelHingeFramework.ofNormals (k := 1) G ends
      (fun p => pencilPicturePoint q p.1 p.2)).toBodyHinge
  rw [Graph.finrank_infinitesimalMotions_ofNormals_pencilPicturePoint hq hends,
    Graph.finrank_liftingPlanes hq, show screwDim 1 = 3 from rfl,
    ← Set.ncard_add_ncard_compl V(G) (Set.toFinite _) (Set.toFinite _)] at hc
  have hz := congrArg (Nat.cast : ℕ → ℤ) hc
  push_cast at hz
  linarith

/-- **The flat lower bound `dim L(q) ≥ 3 + def₂`** (`lem:pencil-lifting-space-deficiency`;
informal (MC-4)(b)). The grade-1 relative deficiency bound
(`BodyHingeFramework.screwDim_mul_compl_add_deficiency_le_finrank_infinitesimalMotions`, at
`bodyBarDim 2 = screwDim 1 = 3`, every hinge nonzero since adjacent picture points differ) bounds
the motions of the plane framework at the normals `(x_v, y_v, 1)` below by
`3(|V(G)ᶜ| + 1) + def₂`; that motion space is `F(q)`, of dimension `3|V(G)ᶜ| + dim L(q)`. -/
theorem _root_.Graph.three_add_deficiency_le_finrank_liftingSpace [Finite α] [Finite β]
    {G : Graph α β} {q : α × Fin 2 → K} (hq : G.IsAdmissiblePicture q) (hV : V(G).Nonempty) :
    3 + G.deficiency 2 ≤ (Module.finrank K (G.liftingSpace q) : ℤ) := by
  classical
  have : Inhabited α := ⟨hV.some⟩
  have hends : ∀ e u v, G.IsLink e u v → G.IsLink e (G.endsOf e).1 (G.endsOf e).2 :=
    fun e _ _ he => G.isLink_endsOf he.edge_mem
  have hhub := (PanelHingeFramework.ofNormals (k := 1) G G.endsOf
      (fun p => pencilPicturePoint q p.1 p.2)).toBodyHinge
    |>.screwDim_mul_compl_add_deficiency_le_finrank_infinitesimalMotions (n := 2) rfl hV
      fun e u v he => by
        rw [PanelHingeFramework.toBodyHinge_supportExtensor_ne_zero_iff]
        exact linearIndependent_pencilPicturePoint_pair (hq.1 e _ _ (hends e u v he))
  rw [Graph.finrank_infinitesimalMotions_ofNormals_pencilPicturePoint hq hends,
    Graph.finrank_liftingPlanes hq] at hhub
  simp only [PanelHingeFramework.toBodyHinge_graph, PanelHingeFramework.ofNormals_graph,
    show screwDim 1 = 3 from rfl] at hhub
  push_cast at hhub
  have : (V(G).compl.ncard : ℤ) = (V(G)ᶜ.ncard : ℤ) := rfl
  linarith

/-! ## Grade 2: the flat split `Λ²K⁴ = W′ ⊕ W_Π` -/

/-- Drop the height coordinate: `(x, y, z, w) ↦ (x, y, w)`. -/
def planarProj : (Fin 4 → K) →ₗ[K] (Fin 3 → K) := LinearMap.funLeft K K ![0, 1, 3]

theorem planarProj_apply (v : Fin 4 → K) : planarProj v = ![v 0, v 1, v 3] := by
  funext i; fin_cases i <;> rfl

theorem planarProj_pencilConfigPoint (q : α × Fin 2 → K) (z : α → K) (w : α) :
    planarProj (pencilConfigPoint q z w) = pencilPicturePoint q w := by
  funext i; fin_cases i <;> rfl

/-- The `W′` coordinate as an alternating form: `σ(v, w) = v_z ŵ − w_z v̂`. -/
def flatSigmaForm : (Fin 4 → K) [⋀^Fin 2]→ₗ[K] (Fin 3 → K) where
  toFun v := (v 0 2) • planarProj (v 1) - (v 1 2) • planarProj (v 0)
  map_update_add' := by
    intro _ m i x y; fin_cases i <;> simp [Function.update, add_smul, map_add] <;> module
  map_update_smul' := by
    intro _ m i c x; fin_cases i <;> simp [Function.update, map_smul] <;> module
  map_eq_zero_of_eq' v i j hij hne := by fin_cases i <;> fin_cases j <;> simp_all

/-- The `W_Π` coordinate as an alternating form: `π(v, w) = v̂ ×₃ ŵ`. -/
def flatPiForm : (Fin 4 → K) [⋀^Fin 2]→ₗ[K] (Fin 3 → K) where
  toFun v := crossProduct (planarProj (v 0)) (planarProj (v 1))
  map_update_add' := by intro _ m i x y; fin_cases i <;> simp [Function.update, map_add]
  map_update_smul' := by intro _ m i c x; fin_cases i <;> simp [Function.update, map_smul]
  map_eq_zero_of_eq' v i j hij hne := by fin_cases i <;> fin_cases j <;> simp_all

/-- **The `W′` coordinate of a screw** (`lem:pencil-flat-split`): the lift of `flatSigmaForm`. -/
noncomputable def flatSigma : ScrewSpace K 2 →ₗ[K] (Fin 3 → K) :=
  (exteriorPower.alternatingMapLinearEquiv flatSigmaForm) ∘ₗ
    (ScrewSpace.equivExteriorPower K 2).toLinearMap

/-- **The `W_Π` coordinate of a screw** (`lem:pencil-flat-split`): the lift of `flatPiForm`. -/
noncomputable def flatPi : ScrewSpace K 2 →ₗ[K] (Fin 3 → K) :=
  (exteriorPower.alternatingMapLinearEquiv flatPiForm) ∘ₗ
    (ScrewSpace.equivExteriorPower K 2).toLinearMap

theorem flatSigma_mk_extensor (a b : Fin 4 → K) :
    flatSigma (ScrewSpace.mk (extensor ![a, b]) (extensor_mem_exteriorPower _))
      = a 2 • planarProj b - b 2 • planarProj a := by
  rw [flatSigma, LinearMap.comp_apply, LinearEquiv.coe_coe, equivExteriorPower_mk_extensor,
    exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  rfl

theorem flatPi_mk_extensor (a b : Fin 4 → K) :
    flatPi (ScrewSpace.mk (extensor ![a, b]) (extensor_mem_exteriorPower _))
      = crossProduct (planarProj a) (planarProj b) := by
  rw [flatPi, LinearMap.comp_apply, LinearEquiv.coe_coe, equivExteriorPower_mk_extensor,
    exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  rfl

/-- The standard basis bivector `e_i ∧ e_j`. -/
private noncomputable def flatStdBiv (i j : Fin 4) : ScrewSpace K 2 :=
  ScrewSpace.mk (extensor ![(Pi.single i 1 : Fin 4 → K), Pi.single j 1])
    (extensor_mem_exteriorPower _)

/-- A preimage of `(s, t)` under `(σ, π)`, spread over the standard basis bivectors. -/
private noncomputable def flatRebuild (p : (Fin 3 → K) × (Fin 3 → K)) : ScrewSpace K 2 :=
  p.1 0 • flatStdBiv 2 0 + p.1 1 • flatStdBiv 2 1 + p.1 2 • flatStdBiv 2 3
    + p.2 0 • flatStdBiv 1 3 - p.2 1 • flatStdBiv 0 3 + p.2 2 • flatStdBiv 0 1

private theorem flatSigma_flatRebuild (p : (Fin 3 → K) × (Fin 3 → K)) :
    flatSigma (flatRebuild p) = p.1 := by
  simp only [flatRebuild, flatStdBiv, map_add, map_sub, map_smul, flatSigma_mk_extensor,
    planarProj_apply]
  funext k; fin_cases k <;> simp

private theorem flatPi_flatRebuild (p : (Fin 3 → K) × (Fin 3 → K)) :
    flatPi (flatRebuild p) = p.2 := by
  simp only [flatRebuild, flatStdBiv, map_add, map_sub, map_smul, flatPi_mk_extensor,
    planarProj_apply]
  funext k; fin_cases k <;> simp [cross_apply]

/-- **The flat split** (`lem:pencil-flat-split`; Phase 40c FLAT): `S ↦ (σ S, π S)` is a linear
equivalence `ScrewSpace K 2 ≃ K³ × K³`, the Plücker split `Λ²K⁴ = W′ ⊕ W_Π` along the plane
`z = 0`. It is surjective by an explicit right inverse and both sides have dimension `6`. -/
noncomputable def flatScrewEquiv : ScrewSpace K 2 ≃ₗ[K] (Fin 3 → K) × (Fin 3 → K) := by
  refine LinearEquiv.ofBijective (flatSigma.prod flatPi) ?_
  have hsurj : Function.Surjective (flatSigma.prod flatPi : ScrewSpace K 2 →ₗ[K] _) :=
    fun p => ⟨flatRebuild p, Prod.ext (flatSigma_flatRebuild p) (flatPi_flatRebuild p)⟩
  refine ⟨?_, hsurj⟩
  rw [LinearMap.injective_iff_surjective_of_finrank_eq_finrank]
  · exact hsurj
  · rw [screwSpace_finrank, Module.finrank_prod, Module.finrank_fin_fun]; rfl

@[simp] theorem flatScrewEquiv_apply (S : ScrewSpace K 2) :
    flatScrewEquiv S = (flatSigma S, flatPi S) := rfl

/-- **The hinge condition at a flat hinge, in split coordinates** (`lem:pencil-flat-split`): for
points `a, b` in the plane `z = 0` with independent projections, a screw lies on the span of
`a ∧ b` exactly when its `W′` coordinate vanishes and its `W_Π` coordinate is orthogonal to both
projections. -/
theorem mem_span_extensor_flat_iff {a b : Fin 4 → K} (ha : a 2 = 0) (hb : b 2 = 0)
    (hab : LinearIndependent K ![planarProj a, planarProj b]) (D : ScrewSpace K 2) :
    D ∈ Submodule.span K {ScrewSpace.mk (extensor ![a, b]) (extensor_mem_exteriorPower _)} ↔
      flatSigma D = 0 ∧ flatPi D ⬝ᵥ planarProj a = 0 ∧ flatPi D ⬝ᵥ planarProj b = 0 := by
  rw [← mem_span_crossProduct_iff hab]
  set C := ScrewSpace.mk (extensor ![a, b]) (extensor_mem_exteriorPower _) with hC
  have hσ : flatSigma C = 0 := by rw [hC, flatSigma_mk_extensor, ha, hb]; simp
  have hπ : flatPi C = crossProduct (planarProj a) (planarProj b) := by
    rw [hC, flatPi_mk_extensor]
  constructor
  · intro hD
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hD
    rw [map_smul, map_smul, hσ, hπ, smul_zero]
    exact ⟨rfl, Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)⟩
  · rintro ⟨h0, hD⟩
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hD
    refine Submodule.mem_span_singleton.mpr ⟨t, flatScrewEquiv.injective ?_⟩
    rw [map_smul, flatScrewEquiv_apply, flatScrewEquiv_apply, hσ, hπ, h0, ← ht, Prod.smul_mk,
      smul_zero]

/-- **The glued block** (`lem:pencil-flat-split`): families `α → K³` equal across every link. -/
def _root_.Graph.linkConstants (G : Graph α β) : Submodule K (α → Fin 3 → K) where
  carrier := {s | ∀ e u v, G.IsLink e u v → s u = s v}
  zero_mem' := fun _ _ _ _ => rfl
  add_mem' := by rintro s t hs ht e u v he; simp [hs e u v he, ht e u v he]
  smul_mem' := by rintro c s hs e u v he; simp [hs e u v he]

/-- **The glued block of a connected graph has dimension `3(|V(G)ᶜ| + 1)`**
(`lem:pencil-flat-split`): a family equal across every link is constant on `V(G)`
(`Graph.Preconnected.eq_of_forall_isLink`) and free off it. -/
theorem _root_.Graph.finrank_linkConstants [Finite α] {G : Graph α β} (hG : G.Connected) :
    Module.finrank K (G.linkConstants (K := K)) = 3 * (V(G)ᶜ.ncard + 1) := by
  classical
  have : Fintype α := Fintype.ofFinite α
  obtain ⟨v₀, hv₀⟩ := hG.nonempty
  let Φ : G.linkConstants (K := K) →ₗ[K] (Fin 3 → K) × (↥(V(G)ᶜ) → Fin 3 → K) :=
    { toFun := fun s => (s.1 v₀, fun w => s.1 w)
      map_add' := fun s t => rfl
      map_smul' := fun c s => rfl }
  have hbij : Function.Bijective Φ := by
    refine ⟨fun s t hst => Subtype.ext (funext fun w => ?_), fun p => ?_⟩
    · by_cases hw : w ∈ V(G)
      · have h1 : s.1 v₀ = t.1 v₀ := congr_arg Prod.fst hst
        rw [hG.pre.eq_of_forall_isLink s.2 hw hv₀, h1, hG.pre.eq_of_forall_isLink t.2 hv₀ hw]
      · exact congr_fun (congr_arg Prod.snd hst) ⟨w, hw⟩
    · refine ⟨⟨fun w => if hw : w ∈ V(G) then p.1 else p.2 ⟨w, hw⟩, fun e u v he => ?_⟩,
        Prod.ext ?_ ?_⟩
      · simp [he.left_mem, he.right_mem]
      · simp [Φ, hv₀]
      · funext ⟨w, hw⟩
        simp [Φ, show w ∉ V(G) from hw]
  rw [(LinearEquiv.ofBijective Φ hbij).finrank_eq, Module.finrank_prod, Module.finrank_fin_fun,
    Module.finrank_pi_fintype]
  have hc : Fintype.card ↥(V(G)ᶜ) = V(G)ᶜ.ncard := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, Module.finrank_fin_fun, hc]
  ring

/-- **The flat motion space splits** (`lem:pencil-flat-split`; Phase 40c FLAT, informal (MC-4)'s
glued block and two-condition block). On a connected graph over an admissible picture, the
motions of the point-join framework of the flat configuration `(q, 0)` are equivalent, through the
pointwise flat split, to the glued block times `F(q)`: at each link the hinge condition reads
`σ S_u = σ S_v` and `π S_u − π S_v` orthogonal to both ends' picture points
(`mem_span_extensor_flat_iff`). -/
theorem _root_.Graph.finrank_infinitesimalMotions_pointJoinFramework_flat [Finite α]
    {G : Graph α β} (hG : G.Connected) {q : α × Fin 2 → K} (hq : G.IsAdmissiblePicture q)
    {ends : β → α × α} (hends : ∀ e u v, G.IsLink e u v → G.IsLink e (ends e).1 (ends e).2) :
    Module.finrank K (pointJoinFramework G ends (pencilConfigPoint q 0)).infinitesimalMotions
      = 3 * (V(G)ᶜ.ncard + 1) + Module.finrank K (G.liftingPlanes q) := by
  set F := pointJoinFramework G ends (pencilConfigPoint q 0)
  have h2 : ∀ w, pencilConfigPoint q (0 : α → K) w 2 = 0 := fun w => rfl
  have hlink : ∀ (S : α → ScrewSpace K 2) e u v, G.IsLink e u v →
      (S u - S v ∈ Submodule.span K {F.supportExtensor e} ↔
        flatSigma (S u) = flatSigma (S v) ∧
        (flatPi (S u) - flatPi (S v)) ⬝ᵥ pencilPicturePoint q u = 0 ∧
        (flatPi (S u) - flatPi (S v)) ⬝ᵥ pencilPicturePoint q v = 0) := by
    intro S e u v he
    change S u - S v ∈ Submodule.span K {ScrewSpace.mk (extensor ![pencilConfigPoint q 0
      (ends e).1, pencilConfigPoint q 0 (ends e).2]) (extensor_mem_exteriorPower _)} ↔ _
    have hli : ∀ {a b : α}, G.IsLink e a b →
        LinearIndependent K ![planarProj (pencilConfigPoint q 0 a),
          planarProj (pencilConfigPoint q 0 b)] := fun hab => by
      rw [planarProj_pencilConfigPoint, planarProj_pencilConfigPoint]
      exact linearIndependent_pencilPicturePoint_pair (hq.1 e _ _ hab)
    rcases (hends e u v he).eq_and_eq_or_eq_and_eq he with ⟨h1, h2'⟩ | ⟨h1, h2'⟩
    · rw [h1, h2', mem_span_extensor_flat_iff (h2 u) (h2 v) (hli he),
        planarProj_pencilConfigPoint, planarProj_pencilConfigPoint, map_sub, map_sub, sub_eq_zero]
    · rw [h1, h2', mem_span_extensor_flat_iff (h2 v) (h2 u) (hli he.symm),
        planarProj_pencilConfigPoint, planarProj_pencilConfigPoint, map_sub, map_sub, sub_eq_zero]
      exact and_congr Iff.rfl and_comm
  let Φ : F.infinitesimalMotions →ₗ[K] (G.linkConstants (K := K)) × (G.liftingPlanes q) :=
    { toFun := fun S => (⟨fun w => flatSigma (S.1 w), fun e u v he =>
          ((hlink S.1 e u v he).mp (S.2 e u v he)).1⟩,
        ⟨fun w => flatPi (S.1 w), fun e u v he =>
          ((hlink S.1 e u v he).mp (S.2 e u v he)).2⟩)
      map_add' := fun S T => by ext w i <;> simp
      map_smul' := fun c S => by ext w i <;> simp }
  -- the pointwise inverse of the flat split
  have hσ : ∀ p : (G.linkConstants (K := K)) × (G.liftingPlanes q), ∀ w,
      flatSigma (flatScrewEquiv.symm (p.1.1 w, p.2.1 w)) = p.1.1 w := fun p w =>
    congr_arg Prod.fst (flatScrewEquiv.apply_symm_apply (p.1.1 w, p.2.1 w))
  have hπ : ∀ p : (G.linkConstants (K := K)) × (G.liftingPlanes q), ∀ w,
      flatPi (flatScrewEquiv.symm (p.1.1 w, p.2.1 w)) = p.2.1 w := fun p w =>
    congr_arg Prod.snd (flatScrewEquiv.apply_symm_apply (p.1.1 w, p.2.1 w))
  have hbij : Function.Bijective Φ := by
    refine ⟨fun S T hST => Subtype.ext (funext fun w => flatScrewEquiv.injective ?_),
      fun p => ⟨⟨fun w => flatScrewEquiv.symm (p.1.1 w, p.2.1 w), fun e u v he =>
        (hlink (fun w => flatScrewEquiv.symm (p.1.1 w, p.2.1 w)) e u v he).mpr ?_⟩, ?_⟩⟩
    · rw [flatScrewEquiv_apply, flatScrewEquiv_apply]
      exact Prod.ext (congr_arg (fun x : _ × _ => x.1.1 w) hST)
        (congr_arg (fun x : _ × _ => x.2.1 w) hST)
    · simp only [hσ, hπ]
      exact ⟨p.1.2 e u v he, p.2.2 e u v he⟩
    · ext w i <;> simp [Φ, hσ, hπ]
  rw [(LinearEquiv.ofBijective Φ hbij).finrank_eq, Module.finrank_prod,
    Graph.finrank_linkConstants hG]

/-- **The flat rank is `6|V(G)| − 3 − dim L(q)`** (`thm:pencil-flat-rank`; informal (MC-4)(a)), at
the rank `Graph.X0Attains` reads, on a connected graph over an admissible picture. The polarity
carries the rank to the point-join framework
(`ofNormals_toBodyHinge_eq_mapSupport_pointJoinFramework`,
`BodyHingeFramework.finrank_span_rigidityRows_mapSupport`), whose motions have dimension
`3(|V(G)ᶜ| + 1) + 3|V(G)ᶜ| + dim L(q)`
(`Graph.finrank_infinitesimalMotions_pointJoinFramework_flat`, `Graph.finrank_liftingPlanes`)
inside the `6|α|`-dimensional screw assignments. -/
theorem _root_.Graph.finrank_span_rigidityRows_ofNormals_flat [Finite α] {G : Graph α β}
    (hG : G.Connected) {q : α × Fin 2 → K} (hq : G.IsAdmissiblePicture q) {ends : β → α × α}
    (hends : ∀ e u v, G.IsLink e u v → G.IsLink e (ends e).1 (ends e).2) :
    (Module.finrank K (Submodule.span K
        (PanelHingeFramework.ofNormals (k := 2) G ends
          (fun p => pencilConfigPoint q 0 p.1 p.2)).toBodyHinge.rigidityRows) : ℤ)
      = screwDim 2 * (V(G).ncard : ℤ) - 3 - Module.finrank K (G.liftingSpace q) := by
  rw [ofNormals_toBodyHinge_eq_mapSupport_pointJoinFramework G ends (pencilConfigPoint q 0),
    BodyHingeFramework.finrank_span_rigidityRows_mapSupport]
  have hc := (pointJoinFramework G ends
    (pencilConfigPoint q 0)).finrank_span_rigidityRows_add_finrank_infinitesimalMotions
  rw [Graph.finrank_infinitesimalMotions_pointJoinFramework_flat hG hq hends,
    Graph.finrank_liftingPlanes hq, show screwDim 2 = 6 from rfl,
    ← Set.ncard_add_ncard_compl V(G) (Set.toFinite _) (Set.toFinite _)] at hc
  rw [show screwDim 2 = 6 from rfl]
  push_cast
  omega

/-! ## The flat configuration attains, and `X₀` attains at the flat witness -/

/-- **The flat rank is at most `6(|V(G)| − 1) − def₂`** (`thm:pencil-flat-rank`; informal
(MC-4)(c)): (MC-4)(a) with (MC-4)(b). -/
theorem _root_.Graph.finrank_span_rigidityRows_ofNormals_flat_le [Finite α] [Finite β]
    {G : Graph α β} (hG : G.Connected) {q : α × Fin 2 → K} (hq : G.IsAdmissiblePicture q)
    {ends : β → α × α} (hends : ∀ e u v, G.IsLink e u v → G.IsLink e (ends e).1 (ends e).2) :
    (Module.finrank K (Submodule.span K
        (PanelHingeFramework.ofNormals (k := 2) G ends
          (fun p => pencilConfigPoint q 0 p.1 p.2)).toBodyHinge.rigidityRows) : ℤ)
      ≤ screwDim 2 * ((V(G).ncard : ℤ) - 1) - G.deficiency 2 := by
  rw [Graph.finrank_span_rigidityRows_ofNormals_flat hG hq hends, show screwDim 2 = 6 from rfl]
  have := Graph.three_add_deficiency_le_finrank_liftingSpace hq hG.nonempty
  push_cast; linarith

/-- **The flat rank attains `6(|V(G)| − 1) − def_n` iff `dim L(q) = 3 + def_n`**
(`thm:pencil-flat-rank` at `n = 2`, the equality case of (MC-4)(c); `cor:pencil-flat-attains` at
`n = 3`, the first equivalence of (MC-5)(ii)). Immediate from (MC-4)(a). -/
theorem _root_.Graph.finrank_span_rigidityRows_ofNormals_flat_eq_iff [Finite α] {G : Graph α β}
    (hG : G.Connected) {q : α × Fin 2 → K} (hq : G.IsAdmissiblePicture q)
    {ends : β → α × α} (hends : ∀ e u v, G.IsLink e u v → G.IsLink e (ends e).1 (ends e).2)
    (n : ℕ) :
    (Module.finrank K (Submodule.span K
        (PanelHingeFramework.ofNormals (k := 2) G ends
          (fun p => pencilConfigPoint q 0 p.1 p.2)).toBodyHinge.rigidityRows) : ℤ)
      = screwDim 2 * ((V(G).ncard : ℤ) - 1) - G.deficiency n ↔
    (Module.finrank K (G.liftingSpace q) : ℤ) = 3 + G.deficiency n := by
  rw [Graph.finrank_span_rigidityRows_ofNormals_flat hG hq hends, show screwDim 2 = 6 from rfl]
  push_cast
  constructor <;> intro h <;> linarith

/-- **`dim L(q) = 3 + def₃` iff equality holds in (MC-4)(b) and `def₂ = def₃`**
(`cor:pencil-flat-attains`; the second equivalence of informal (MC-5)(ii)), from
`3 + def₂ ≤ dim L(q)` and `def₃ ≤ def₂`. -/
theorem _root_.Graph.finrank_liftingSpace_eq_three_add_deficiency_three_iff [Finite α] [Finite β]
    {G : Graph α β} (hG : G.Connected) {q : α × Fin 2 → K} (hq : G.IsAdmissiblePicture q) :
    (Module.finrank K (G.liftingSpace q) : ℤ) = 3 + G.deficiency 3 ↔
      (Module.finrank K (G.liftingSpace q) : ℤ) = 3 + G.deficiency 2 ∧
        G.deficiency 2 = G.deficiency 3 := by
  have hb := Graph.three_add_deficiency_le_finrank_liftingSpace hq hG.nonempty
  have hi := hG.deficiency_three_le_deficiency_two
  exact ⟨fun h => ⟨by linarith, by linarith⟩, fun ⟨h1, h2⟩ => by linarith⟩

/-- **`X₀` attains at the flat witness** (`cor:pencil-flat-attains`; informal (MC-5)(ii)'s `⇐`
with the one-witness principle). If an admissible picture has `dim L(q) ≤ 3 + def₃`, it is a main
picture — every admissible picture has `dim L ≥ 3 + def₂ ≥ 3 + def₃`
(`Graph.three_add_deficiency_le_finrank_liftingSpace`,
`Graph.Connected.deficiency_three_le_deficiency_two`) — and its flat configuration has rank at
least the target (`Graph.finrank_span_rigidityRows_ofNormals_flat`), so `Graph.x0Attains_of_exists`
applies at the height `0 ∈ L(q)`. -/
theorem _root_.Graph.x0Attains_of_finrank_liftingSpace_le [Finite α] [Finite β] {G : Graph α β}
    (hG : G.Connected) {q : α × Fin 2 → K} (hq : G.IsAdmissiblePicture q)
    (hL : (Module.finrank K (G.liftingSpace q) : ℤ) ≤ 3 + G.deficiency 3) : G.X0Attains K := by
  classical
  have hV := hG.nonempty
  have : Inhabited α := ⟨hV.some⟩
  have hends : ∀ e u v, G.IsLink e u v → G.IsLink e (G.endsOf e).1 (G.endsOf e).2 :=
    fun e _ _ he => G.isLink_endsOf he.edge_mem
  have hdef := hG.deficiency_three_le_deficiency_two
  have hmain : G.IsMainPicture q := by
    refine ⟨hq, fun q' hq' => ?_⟩
    have := Graph.three_add_deficiency_le_finrank_liftingSpace hq' hV
    have : (Module.finrank K (G.liftingSpace q) : ℤ) ≤ Module.finrank K (G.liftingSpace q') := by
      linarith
    exact_mod_cast this
  refine Graph.x0Attains_of_exists hV G.endsOf hends hmain (G.liftingSpace q).zero_mem ?_
  rw [Graph.finrank_span_rigidityRows_ofNormals_flat hG hq hends, show screwDim 2 = 6 from rfl]
  push_cast; linarith

/-- **A flat main component attains** (`cor:pencil-flat-x0`; informal (MC-5)(iii)). If
`dim L(q) = 3` at an admissible picture (so `ℓ₀ = 3`), then `def₂ = def₃ = 0`
(`Graph.three_add_deficiency_le_finrank_liftingSpace`,
`Graph.Connected.deficiency_three_le_deficiency_two`, both nonnegative) and `X₀` attains
(`Graph.x0Attains_of_finrank_liftingSpace_le`). -/
theorem _root_.Graph.x0Attains_of_finrank_liftingSpace_eq_three [Finite α] [Finite β]
    {G : Graph α β} (hG : G.Connected) {q : α × Fin 2 → K} (hq : G.IsAdmissiblePicture q)
    (h3 : Module.finrank K (G.liftingSpace q) = 3) :
    G.deficiency 2 = 0 ∧ G.deficiency 3 = 0 ∧ G.X0Attains K := by
  have hb := Graph.three_add_deficiency_le_finrank_liftingSpace hq hG.nonempty
  have hi := hG.deficiency_three_le_deficiency_two
  have h0 := G.deficiency_nonneg 3 hG.nonempty
  rw [h3] at hb
  push_cast at hb
  refine ⟨by linarith, by linarith, Graph.x0Attains_of_finrank_liftingSpace_le hG hq ?_⟩
  rw [h3]; push_cast; linarith

/-- **A flat fibre makes the flat configuration rigid** (`cor:pencil-flat-x0`; the rank clause of
informal (MC-5)(iii)): at `dim L(q) = 3` the flat rank (MC-4)(a) is `6(|V(G)| − 1)`. -/
theorem _root_.Graph.finrank_span_rigidityRows_ofNormals_flat_of_finrank_eq_three [Finite α]
    {G : Graph α β} (hG : G.Connected) {q : α × Fin 2 → K} (hq : G.IsAdmissiblePicture q)
    {ends : β → α × α} (hends : ∀ e u v, G.IsLink e u v → G.IsLink e (ends e).1 (ends e).2)
    (h3 : Module.finrank K (G.liftingSpace q) = 3) :
    (Module.finrank K (Submodule.span K
        (PanelHingeFramework.ofNormals (k := 2) G ends
          (fun p => pencilConfigPoint q 0 p.1 p.2)).toBodyHinge.rigidityRows) : ℤ)
      = screwDim 2 * ((V(G).ncard : ℤ) - 1) := by
  rw [Graph.finrank_span_rigidityRows_ofNormals_flat hG hq hends, h3, show screwDim 2 = 6 from rfl]
  push_cast; ring


/-! ## Joins of two points in flat coordinates (Phase 40g CHAIN)

The hinge `pointJoinFramework` places at a link is the join of the two configuration points, and
the flat split `flatScrewEquiv` reads it as `(p_z p̄′ − p′_z p̄, p̄ × p̄′)`, `p̄` the planar part
(`lem:pencil-join-flat`). So independence of a family of joins is a question about integer vectors
when the points have integer coordinates (`MainComponent/Ear.lean`'s certificates). -/

/-- **The join `p ∧ p'` of two points of `K⁴`, as a screw** (Phase 40g CHAIN,
`lem:pencil-join-flat`): the hinge of `pointJoinFramework` at a link with those end points. -/
noncomputable def pointJoin (p p' : Fin 4 → K) : ScrewSpace K 2 :=
  ScrewSpace.mk (extensor ![p, p']) (extensor_mem_exteriorPower _)

/-- **A join in flat coordinates** (`lem:pencil-join-flat`): `p ∧ p'` is sent to
`(p_z p̄′ − p′_z p̄, p̄ × p̄′)`, where `p̄ = planarProj p`. -/
theorem flatScrewEquiv_pointJoin (p p' : Fin 4 → K) :
    flatScrewEquiv (pointJoin p p')
      = (p 2 • planarProj p' - p' 2 • planarProj p,
        crossProduct (planarProj p) (planarProj p')) := by
  rw [flatScrewEquiv_apply, pointJoin, flatSigma_mk_extensor, flatPi_mk_extensor]

/-- The `W′` coordinate of a join: `σ(p ∧ p') = p_z p̄′ − p′_z p̄`. -/
theorem flatSigma_pointJoin (p p' : Fin 4 → K) :
    flatSigma (pointJoin p p') = p 2 • planarProj p' - p' 2 • planarProj p :=
  flatSigma_mk_extensor p p'

/-- The `W_Π` coordinate of a join: `π(p ∧ p') = p̄ ×₃ p̄′`. -/
theorem flatPi_pointJoin (p p' : Fin 4 → K) :
    flatPi (pointJoin p p') = crossProduct (planarProj p) (planarProj p') :=
  flatPi_mk_extensor p p'

/-- The join is antisymmetric: `p′ ∧ p = −(p ∧ p′)` (Phase 40h SHORT). -/
theorem pointJoin_swap (p p' : Fin 4 → K) : pointJoin p' p = -pointJoin p p' := by
  refine (flatScrewEquiv (K := K)).injective ?_
  rw [map_neg, flatScrewEquiv_pointJoin, flatScrewEquiv_pointJoin, Prod.neg_mk, neg_sub,
    ← cross_anticomm]

/-- The join of a point with itself vanishes: `p ∧ p = 0` (Phase 40h SHORT). -/
theorem pointJoin_self (p : Fin 4 → K) : pointJoin p p = 0 :=
  (flatScrewEquiv (K := K)).injective <| by
    rw [flatScrewEquiv_pointJoin, sub_self, cross_self, map_zero, Prod.mk_zero_zero]

/-- The join is linear in its first point along a line:
`(p + t r) ∧ p′ = p ∧ p′ + t (r ∧ p′)` (Phase 40h SHORT). -/
theorem pointJoin_add_smul_left (p r p' : Fin 4 → K) (t : K) :
    pointJoin (p + t • r) p' = pointJoin p p' + t • pointJoin r p' := by
  refine (flatScrewEquiv (K := K)).injective ?_
  simp only [map_add, map_smul, flatScrewEquiv_pointJoin, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, LinearMap.add_apply, LinearMap.smul_apply, Prod.smul_mk, Prod.mk_add_mk]
  congr 1
  module

/-- The join vanishes when its first point is the origin: `0 ∧ p' = 0` (Phase 40i ORBIT). -/
theorem pointJoin_zero_left (p' : Fin 4 → K) : pointJoin 0 p' = 0 := by
  have := pointJoin_add_smul_left 0 0 p' 1
  simp only [add_zero, smul_zero, one_smul] at this
  exact left_eq_add.mp this

/-- The join is additive in its first point: `(p + r) ∧ p′ = p ∧ p′ + r ∧ p′` (Phase 40i ORBIT). -/
theorem pointJoin_add_left (p r p' : Fin 4 → K) :
    pointJoin (p + r) p' = pointJoin p p' + pointJoin r p' := by
  simpa using pointJoin_add_smul_left p r p' 1

/-- The join is homogeneous in its first point: `(c • p) ∧ p′ = c • (p ∧ p′)` (Phase 40i ORBIT). -/
theorem pointJoin_smul_left (c : K) (p p' : Fin 4 → K) :
    pointJoin (c • p) p' = c • pointJoin p p' := by
  have := pointJoin_add_smul_left 0 p p' c
  rwa [zero_add, pointJoin_zero_left, zero_add] at this

/-- The join is subtractive in its first point: `(p − r) ∧ p′ = p ∧ p′ − r ∧ p′`
(Phase 40i ORBIT). -/
theorem pointJoin_sub_left (p r p' : Fin 4 → K) :
    pointJoin (p - r) p' = pointJoin p p' - pointJoin r p' := by
  rw [sub_eq_add_neg, pointJoin_add_left, ← neg_one_smul K r, pointJoin_smul_left]
  module

/-- The join is additive in its second point: `p′ ∧ (p + r) = p′ ∧ p + p′ ∧ r`
(Phase 40i ORBIT). -/
theorem pointJoin_add_right (p r p' : Fin 4 → K) :
    pointJoin p' (p + r) = pointJoin p' p + pointJoin p' r := by
  rw [pointJoin_swap, pointJoin_add_left, pointJoin_swap p p', pointJoin_swap r p']
  abel

/-- The join is homogeneous in its second point: `p′ ∧ (c • p) = c • (p′ ∧ p)`
(Phase 40i ORBIT). -/
theorem pointJoin_smul_right (c : K) (p p' : Fin 4 → K) :
    pointJoin p' (c • p) = c • pointJoin p' p := by
  rw [pointJoin_swap, pointJoin_smul_left, pointJoin_swap p p', smul_neg]

/-- The join is subtractive in its second point: `p′ ∧ (p − r) = p′ ∧ p − p′ ∧ r`
(Phase 40i ORBIT). -/
theorem pointJoin_sub_right (p r p' : Fin 4 → K) :
    pointJoin p' (p - r) = pointJoin p' p - pointJoin p' r := by
  rw [pointJoin_swap, pointJoin_sub_left, pointJoin_swap p p', pointJoin_swap r p']
  abel

/-- A join is unchanged by moving its second point along the first:
`y ∧ (v + c y) = y ∧ v` (Phase 40h SHORT). -/
theorem pointJoin_add_smul_self_right (y v : Fin 4 → K) (c : K) :
    pointJoin y (v + c • y) = pointJoin y v := by
  rw [pointJoin_swap (v + c • y) y, pointJoin_add_smul_left, pointJoin_self, smul_zero, add_zero,
    ← pointJoin_swap]

/-- **Independence of joins is read in flat coordinates** (`lem:pencil-join-flat`): a family of
joins is linearly independent when the family of its flat coordinates is. -/
theorem linearIndependent_pointJoin_of_flat {ι : Type*} {p p' : ι → Fin 4 → K}
    {w : ι → (Fin 3 → K) × (Fin 3 → K)} (hw : LinearIndependent K w)
    (hpw : ∀ i, (p i 2 • planarProj (p' i) - p' i 2 • planarProj (p i),
      crossProduct (planarProj (p i)) (planarProj (p' i))) = w i) :
    LinearIndependent K (fun i => pointJoin (p i) (p' i)) := by
  have hcomp : ((flatScrewEquiv (K := K)).toLinearMap) ∘
      (fun i => pointJoin (p i) (p' i)) = w := by
    funext i
    simp only [Function.comp_apply, LinearEquiv.coe_coe]
    rw [flatScrewEquiv_pointJoin, hpw]
  exact LinearIndependent.of_comp (flatScrewEquiv (K := K)).toLinearMap (hcomp ▸ hw)

/-- **Three configuration points over independent picture points are independent**
(Phase 40i ORBIT): the planar projection sends them to the picture points. -/
theorem linearIndependent_pencilConfigPoint_triple {q : α × Fin 2 → K} (z : α → K) {u v w : α}
    (h : LinearIndependent K ![pencilPicturePoint q u, pencilPicturePoint q v,
      pencilPicturePoint q w]) :
    LinearIndependent K ![pencilConfigPoint q z u, pencilConfigPoint q z v,
      pencilConfigPoint q z w] := by
  refine LinearIndependent.of_comp (planarProj (K := K)) ?_
  convert h using 1
  funext i
  fin_cases i <;> simp [planarProj_pencilConfigPoint]

/-! ## Independence of joins is Zariski-open (Phase 40g CHAIN)

The flat coordinates of a join of two configuration points are polynomials in the picture at fixed
heights (`joinPicturePoly`) and in the heights at a fixed picture (`joinHeightPoly`), so a nonzero
maximal minor of their coordinate matrix is a polynomial that keeps the joins independent off its
zero set (`lem:pencil-join-independence-open`). -/

/-- **The flat coordinates of a screw**, as one function on `Fin 3 ⊕ Fin 3`: `flatScrewEquiv`
followed by the sum-product split. -/
noncomputable def flatCoords : ScrewSpace K 2 ≃ₗ[K] (Fin 3 ⊕ Fin 3 → K) :=
  (flatScrewEquiv (K := K)).trans (LinearEquiv.sumArrowLequivProdArrow (Fin 3) (Fin 3) K K).symm

/-- The first three flat coordinates of a join: `p_z p̄′ − p′_z p̄`. -/
theorem flatCoords_pointJoin_inl (p p' : Fin 4 → K) (j : Fin 3) :
    flatCoords (pointJoin p p') (Sum.inl j) = (p 2 • planarProj p' - p' 2 • planarProj p) j := by
  rw [flatCoords, LinearEquiv.trans_apply, flatScrewEquiv_pointJoin]
  rfl

/-- The last three flat coordinates of a join: `p̄ × p̄′`. -/
theorem flatCoords_pointJoin_inr (p p' : Fin 4 → K) (j : Fin 3) :
    flatCoords (pointJoin p p') (Sum.inr j) = crossProduct (planarProj p) (planarProj p') j := by
  rw [flatCoords, LinearEquiv.trans_apply, flatScrewEquiv_pointJoin]
  rfl

/-- The screw space of `K⁴` has dimension `3 + 3`, the split `flatCoords` indexes. -/
theorem finrank_screwSpace_two : Module.finrank K (ScrewSpace K 2) = 3 + 3 := by
  rw [screwSpace_finrank]; rfl

/-- Evaluating a cross product of polynomial vectors is the cross product of the evaluations. -/
theorem eval_crossProduct {σ : Type*} (x : σ → K) (A B : Fin 3 → MvPolynomial σ K) (j : Fin 3) :
    MvPolynomial.eval x (crossProduct A B j)
      = crossProduct (fun t => MvPolynomial.eval x (A t))
        (fun t => MvPolynomial.eval x (B t)) j := by
  fin_cases j <;> simp [cross_apply]

/-- **The flat coordinates of a join, as polynomials in the picture**: the join of the
configuration points of `u` and `w` at fixed heights `z`. -/
noncomputable def joinPicturePoly (z : α → K) (u w : α) :
    Fin 3 ⊕ Fin 3 → MvPolynomial (α × Fin 2) K
  | Sum.inl j => MvPolynomial.C (z u) * pencilPicturePointPoly w j
      - MvPolynomial.C (z w) * pencilPicturePointPoly u j
  | Sum.inr j => crossProduct (pencilPicturePointPoly u) (pencilPicturePointPoly w) j

/-- `joinPicturePoly` evaluates at a picture to the flat coordinates of the join there. -/
theorem eval_joinPicturePoly (q : α × Fin 2 → K) (z : α → K) (u w : α) (t : Fin 3 ⊕ Fin 3) :
    MvPolynomial.eval q (joinPicturePoly z u w t)
      = flatCoords (pointJoin (pencilConfigPoint q z u) (pencilConfigPoint q z w)) t := by
  rcases t with j | j
  · rw [flatCoords_pointJoin_inl, planarProj_pencilConfigPoint, planarProj_pencilConfigPoint]
    simp only [joinPicturePoly, map_sub, map_mul, MvPolynomial.eval_C, eval_pencilPicturePointPoly,
      Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rfl
  · rw [flatCoords_pointJoin_inr, planarProj_pencilConfigPoint, planarProj_pencilConfigPoint]
    simp only [joinPicturePoly, eval_crossProduct, eval_pencilPicturePointPoly]

/-- **The flat coordinates of a join, as polynomials in the heights**: the join of the
configuration points of `u` and `w` at a fixed picture `q`. -/
noncomputable def joinHeightPoly (q : α × Fin 2 → K) (u w : α) :
    Fin 3 ⊕ Fin 3 → MvPolynomial α K
  | Sum.inl j => MvPolynomial.X u * MvPolynomial.C (pencilPicturePoint q w j)
      - MvPolynomial.X w * MvPolynomial.C (pencilPicturePoint q u j)
  | Sum.inr j => MvPolynomial.C (crossProduct (pencilPicturePoint q u) (pencilPicturePoint q w) j)

/-- `joinHeightPoly` evaluates at heights to the flat coordinates of the join there. -/
theorem eval_joinHeightPoly (q : α × Fin 2 → K) (z : α → K) (u w : α) (t : Fin 3 ⊕ Fin 3) :
    MvPolynomial.eval z (joinHeightPoly q u w t)
      = flatCoords (pointJoin (pencilConfigPoint q z u) (pencilConfigPoint q z w)) t := by
  rcases t with j | j
  · rw [flatCoords_pointJoin_inl, planarProj_pencilConfigPoint, planarProj_pencilConfigPoint]
    simp only [joinHeightPoly, map_sub, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X,
      Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rfl
  · rw [flatCoords_pointJoin_inr, planarProj_pencilConfigPoint, planarProj_pencilConfigPoint]
    simp only [joinHeightPoly, MvPolynomial.eval_C]

/-- **Independence of joins is Zariski-open in the picture** (`lem:pencil-join-independence-open`,
heights fixed): joins independent at `q₀` stay independent off the zero set of a polynomial in the
picture nonzero at `q₀`, a nonzero maximal minor of `joinPicturePoly`
(`exists_polynomial_ne_zero_of_linearIndependent_at_reindex`). -/
theorem exists_mvPolynomial_linearIndependent_pointJoin_picture {ι : Type*} [Finite ι]
    (z : α → K) (u v : ι → α) {q₀ : α × Fin 2 → K}
    (h : LinearIndependent K
      (fun i => pointJoin (pencilConfigPoint q₀ z (u i)) (pencilConfigPoint q₀ z (v i)))) :
    ∃ P : MvPolynomial (α × Fin 2) K, MvPolynomial.eval q₀ P ≠ 0 ∧
      ∀ q, MvPolynomial.eval q P ≠ 0 → LinearIndependent K
        (fun i => pointJoin (pencilConfigPoint q z (u i)) (pencilConfigPoint q z (v i))) := by
  set e : Fin (Module.finrank K (ScrewSpace K 2)) ≃ (Fin 3 ⊕ Fin 3) :=
    (finCongr finrank_screwSpace_two).trans finSumFinEquiv.symm with he
  set g : (α × Fin 2 → K) → ι → ScrewSpace K 2 :=
    fun q i => pointJoin (pencilConfigPoint q z (u i)) (pencilConfigPoint q z (v i)) with hgdef
  set c : ι → Fin 3 ⊕ Fin 3 → MvPolynomial (α × Fin 2) K :=
    fun i => joinPicturePoly z (u i) (v i) with hcdef
  have hg : ∀ q i t, flatCoords (g q i) t = MvPolynomial.eval q (c i t) := fun q i t =>
    (eval_joinPicturePoly q z (u i) (v i) t).symm
  have h' : LinearIndependent K (fun i : (Set.univ : Set ι) => g q₀ i) :=
    h.comp Subtype.val Subtype.val_injective
  obtain ⟨P, hP₀, hP⟩ := exists_polynomial_ne_zero_of_linearIndependent_at_reindex
    (W := ScrewSpace K 2) e g c flatCoords hg (s := Set.univ) h'
  refine ⟨P, hP₀, fun q hq => ?_⟩
  have := hP q hq
  exact this.comp (fun i => ⟨i, trivial⟩) (fun _ _ h => congrArg Subtype.val h)

/-- **Independence of joins is Zariski-open in the heights** (`lem:pencil-join-independence-open`,
picture fixed): joins independent at `z₀` stay independent off the zero set of a polynomial in the
heights nonzero at `z₀`, a nonzero maximal minor of `joinHeightPoly`. -/
theorem exists_mvPolynomial_linearIndependent_pointJoin_heights {ι : Type*} [Finite ι]
    (q : α × Fin 2 → K) (u v : ι → α) {z₀ : α → K}
    (h : LinearIndependent K
      (fun i => pointJoin (pencilConfigPoint q z₀ (u i)) (pencilConfigPoint q z₀ (v i)))) :
    ∃ R : MvPolynomial α K, MvPolynomial.eval z₀ R ≠ 0 ∧
      ∀ z, MvPolynomial.eval z R ≠ 0 → LinearIndependent K
        (fun i => pointJoin (pencilConfigPoint q z (u i)) (pencilConfigPoint q z (v i))) := by
  set e : Fin (Module.finrank K (ScrewSpace K 2)) ≃ (Fin 3 ⊕ Fin 3) :=
    (finCongr finrank_screwSpace_two).trans finSumFinEquiv.symm with he
  set g : (α → K) → ι → ScrewSpace K 2 :=
    fun z i => pointJoin (pencilConfigPoint q z (u i)) (pencilConfigPoint q z (v i)) with hgdef
  set c : ι → Fin 3 ⊕ Fin 3 → MvPolynomial α K :=
    fun i => joinHeightPoly q (u i) (v i) with hcdef
  have hg : ∀ z i t, flatCoords (g z i) t = MvPolynomial.eval z (c i t) := fun z i t =>
    (eval_joinHeightPoly q z (u i) (v i) t).symm
  have h' : LinearIndependent K (fun i : (Set.univ : Set ι) => g z₀ i) :=
    h.comp Subtype.val Subtype.val_injective
  obtain ⟨R, hR₀, hR⟩ := exists_polynomial_ne_zero_of_linearIndependent_at_reindex
    (W := ScrewSpace K 2) e g c flatCoords hg (s := Set.univ) h'
  refine ⟨R, hR₀, fun z hz => ?_⟩
  have := hR z hz
  exact this.comp (fun i => ⟨i, trivial⟩) (fun _ _ h => congrArg Subtype.val h)

end CombinatorialRigidity.Molecular
