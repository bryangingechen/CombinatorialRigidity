/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.Molecule.Pencil.MainComponent.Bridge

/-!
# Cut vertices and bridges in the `X₀` induction (Phase 40e CUTBRIDGE)

The first two steps of the `X₀` induction (`blueprint/src/chapter/main-component.tex`,
`sec:main-component-cut`; informal (MC-52) and (MC-53), the "if" halves). Every step shares one
contract: it concludes `Graph.X0Attains K` at `G` from `Graph.X0Attains K` at smaller graphs on
the same `α`, `β`. It picks one picture generic for the pieces and main for `G`, finds heights
inside the single lifting space `L_G(q)` where two nonempty Zariski-open conditions meet
(`MvPolynomial.exists_mem_eval_ne_zero₂`), and ends at `Graph.x0Attains_of_exists`. At a cut vertex
and at a bridge the graph is a fibre product of its two sides, so attaining passes from the sides
to `G`.

## Main statements

* `Graph.IsX0Graph` — the standing hypotheses (H): simple, connected, every degree at least two;
  `Graph.IsX0Graph.three_le_ncard_closedNbhd` gives the closed-neighbourhood bound `h3` from it.
* `PanelHingeFramework.finrank_span_rigidityRows_ofNormals_congr` — the row rank reads the normals
  only on `V(G)`, and the selector only up to the orientation of each link.
* `Graph.liftingRestrict`, `Graph.liftingRestrict_mem_liftingSpace`,
  `pencilConfigPoint_liftingRestrict` — a height restricted to a subgraph's bodies is a height of
  the subgraph, with the same configuration points there; `restrictPoly` / `eval_restrictPoly`
  read a polynomial in the heights on the restriction.
* `Graph.exists_liftingRestrict_eq_of_cutVertex` — at a cut vertex the restriction is onto, at
  every picture ((MC-52)(iii)).
* `Graph.X0Attains.of_cutVertex` — **CUT** ((MC-52)(iv), the "if" half), from the rank identity
  `BodyHingeFramework.finrank_span_rigidityRows_cutVertex_eq` (`RigidityMatrix/Bricks.lean`) and
  the deficiency law `Graph.deficiency_add_le_of_cutVertex` (`Molecular/Deficiency.lean`).
* `exists_dotProduct_eq_of_linearIndependent`, `Graph.exists_liftingRestrict_eq_of_bridge`,
  `Graph.X0Attains.of_bridge` — the single bridge ((MC-53) with no path bodies), from the cut-edge
  rank brick `BodyHingeFramework.le_finrank_span_rigidityRows_of_cut` and KT Lemma 3.6
  `Graph.deficiency_eq_of_cutEdges_ncard_le_one`.
* `pathVertex` — the path's extended vertex sequence `a, x 0, …, x (k - 1), b`.
* `Graph.exists_liftingRestrict_eq_of_bridgePath` — restriction is onto at a chain of bridges of
  any length `k` ((MC-53)(iii), `lem:pencil-bridge-fibre`): a single affine extension by the
  witness at `a`, needing no admissibility of the picture and no case split on `k`.

## Design

* **The pieces are induced subgraphs of `G`**, in the same `Graph α β`, described by vertex sets
  and an edge-separation hypothesis `hsep`; nothing of the pieces is used beyond `X0Attains`.
* **One selector for every piece.** The pieces' own selectors are carried to `G.endsOf` by the
  rank congruence, and the restricted heights to the unrestricted ones by
  `pencilConfigPoint_liftingRestrict`, so the three ranks are read at one framework.
* The "only if" halves of (MC-52)(iv) and (MC-53)(iv) are a tracked item, not formalized here
  (`notes/Phase40e.md`).
* **The chain-of-bridges fibre lemma needs only that `a` is `V₁`'s unique gateway.** Extending
  `z₁` by the single affine function already witnessing its own condition at `a` matches every
  closed neighbourhood outside `V₁`, whether it lies entirely there or meets `V₁` only at `a` —
  the interior path bodies' own admissibility (three non-collinear points) and the picture's
  admissibility are never used for this direction, and no case split on `k` is needed. Build 2
  keeps this lemma minimal (no `V₂`, no exact vertex count, no injectivity of `x`): those join the
  hypothesis bundle where the theorem's rank/deficiency count needs them (`notes/Phase40e.md`).
-/

open scoped Graph

namespace CombinatorialRigidity.Molecular

variable {K : Type*} [Field K] {α β : Type*}

/-! ## The standing hypotheses (H) -/

/-- **The standing hypotheses (H)** of the `X₀` induction (`def:pencil-x0-standing`; the header of
informal §(K-main)): `G` is simple and connected, and every body has degree at least two. -/
structure _root_.Graph.IsX0Graph (G : Graph α β) : Prop where
  simple : G.Simple
  connected : G.Connected
  two_le_degree : ∀ v ∈ V(G), 2 ≤ G.degree v

/-- **`h3` from (H)** (`def:pencil-x0-standing`): every closed neighbourhood of a graph satisfying
the standing hypotheses has at least three members (`Graph.three_le_ncard_closedNbhd`). -/
theorem _root_.Graph.IsX0Graph.three_le_ncard_closedNbhd [Finite α] {G : Graph α β}
    (hG : G.IsX0Graph) : ∀ v ∈ V(G), 3 ≤ (G.closedNbhd v).ncard :=
  fun _ hv => Graph.three_le_ncard_closedNbhd hG.simple (hG.two_le_degree _ hv)

/-! ## The row rank reads the normals only on `V(G)` -/

/-- **Rank congruence** (`lem:pencil-rank-congr`). Two selectors recording every link of `G`, and
two normal assignments agreeing on the bodies of `G`, give the same row rank: the hinge at a link
is built from the normals at its two ends and swapping them negates it, so the motion spaces
agree. -/
theorem PanelHingeFramework.finrank_span_rigidityRows_ofNormals_congr {k : ℕ} [Finite α]
    (G : Graph α β) {ends ends' : β → α × α}
    (hends : ∀ e u v, G.IsLink e u v → G.IsLink e (ends e).1 (ends e).2)
    (hends' : ∀ e u v, G.IsLink e u v → G.IsLink e (ends' e).1 (ends' e).2)
    {q q' : α × Fin (k + 2) → K} (hq : ∀ x ∈ V(G), ∀ i, q (x, i) = q' (x, i)) :
    Module.finrank K (Submodule.span K
        (PanelHingeFramework.ofNormals G ends q).toBodyHinge.rigidityRows)
      = Module.finrank K (Submodule.span K
        (PanelHingeFramework.ofNormals G ends' q').toBodyHinge.rigidityRows) := by
  have hmot : (PanelHingeFramework.ofNormals G ends q).toBodyHinge.infinitesimalMotions
      = (PanelHingeFramework.ofNormals G ends' q').toBodyHinge.infinitesimalMotions := by
    refine BodyHingeFramework.infinitesimalMotions_eq_of_isLink_span_supportExtensor _ _ rfl ?_
    intro e u v he
    have h1 := hends e u v he
    have h2 := hends' e u v he
    have hnorm : ∀ x ∈ V(G), (fun i => q' (x, i)) = (fun i => q (x, i)) :=
      fun x hx => funext fun i => (hq x hx i).symm
    simp only [PanelHingeFramework.toBodyHinge_supportExtensor,
      PanelHingeFramework.ofNormals_normal, PanelHingeFramework.ofNormals_ends]
    rw [hnorm _ h2.left_mem, hnorm _ h2.right_mem]
    rcases h2.eq_and_eq_or_eq_and_eq h1 with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · rw [ha, hb]
    · rw [ha, hb, panelSupportExtensor_swap, ← Set.neg_singleton, Submodule.span_neg]
  rw [BodyHingeFramework.span_rigidityRows_eq_dualAnnihilator_infinitesimalMotions,
    BodyHingeFramework.span_rigidityRows_eq_dualAnnihilator_infinitesimalMotions, hmot]

/-! ## Heights restrict to a subgraph -/

open Classical in
/-- **The restriction of heights to a vertex set** (`lem:pencil-lifting-restrict`): `z` on `X`,
zero off it. -/
noncomputable def _root_.Graph.liftingRestrict (X : Set α) : (α → K) →ₗ[K] (α → K) where
  toFun z w := if w ∈ X then z w else 0
  map_add' z₁ z₂ := by funext w; by_cases hw : w ∈ X <;> simp [hw]
  map_smul' c z := by funext w; by_cases hw : w ∈ X <;> simp [hw]

open Classical in
theorem _root_.Graph.liftingRestrict_apply (X : Set α) (z : α → K) (w : α) :
    Graph.liftingRestrict X z w = if w ∈ X then z w else 0 := rfl

/-- **Restriction to a subgraph** (`lem:pencil-lifting-restrict`; (MC-52)(iii)'s restriction map):
a closed neighbourhood of `G′ ≤ G` lies in the one of `G`, so restricting a height of `G` to
`V(G′)` gives a height of `G′`. No hypothesis on the picture. -/
theorem _root_.Graph.liftingRestrict_mem_liftingSpace {G G' : Graph α β} (hle : G' ≤ G)
    {q : α × Fin 2 → K} {z : α → K} (hz : z ∈ G.liftingSpace q) :
    Graph.liftingRestrict V(G') z ∈ G'.liftingSpace q := by
  classical
  refine ⟨fun w hw => by simp [Graph.liftingRestrict_apply, hw], fun v hv => ?_⟩
  obtain ⟨h, hh⟩ := hz.2 v (hle.vertexSet_mono hv)
  refine ⟨h, fun w hw => ?_⟩
  have hwV : w ∈ V(G') := Graph.closedNbhd_subset_vertexSet hv hw
  have hwG : w ∈ G.closedNbhd v := by
    rcases hw with rfl | ⟨e, he⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨e, he.of_le hle⟩
  rw [Graph.liftingRestrict_apply, ite_eq_left hwV]
  exact hh w hwG

/-- **The configuration points of `z` and of its restriction agree on `X`**
(`lem:pencil-lifting-restrict`). -/
theorem pencilConfigPoint_liftingRestrict (X : Set α) (q : α × Fin 2 → K) (z : α → K) {x : α}
    (hx : x ∈ X) (i : Fin 4) :
    pencilConfigPoint q (Graph.liftingRestrict X z) x i = pencilConfigPoint q z x i := by
  classical
  fin_cases i <;> simp [pencilConfigPoint, Graph.liftingRestrict_apply, hx]

open Classical in
/-- **A polynomial in the heights, read on the restriction to `X`**
(`lem:pencil-lifting-restrict`): the variables off `X` are set to zero. -/
noncomputable def restrictPoly (X : Set α) (R : MvPolynomial α K) : MvPolynomial α K :=
  MvPolynomial.bind₁ (fun w => if w ∈ X then MvPolynomial.X w else 0) R

/-- **`restrictPoly` evaluates on the restriction** (`lem:pencil-lifting-restrict`). -/
theorem eval_restrictPoly (X : Set α) (R : MvPolynomial α K) (z : α → K) :
    MvPolynomial.eval z (restrictPoly X R) = MvPolynomial.eval (Graph.liftingRestrict X z) R := by
  classical
  rw [restrictPoly, MvPolynomial.eval_bind₁]
  refine congrArg (fun f => MvPolynomial.eval f R) ?_
  funext w
  by_cases hw : w ∈ X <;> simp [hw, Graph.liftingRestrict_apply]

/-! ## A cut vertex -/

/-- **Restriction is onto at a cut vertex** (`lem:pencil-cut-fibre`; (MC-52)(iii)), at every
picture. Extend `z₁ ∈ L_{G[V₁]}(q)` across `V₂` by the affine function of its closed neighbourhood
at `v`; every closed neighbourhood of `G` lies on one side or, at `v`, meets both in that affine
function. -/
theorem _root_.Graph.exists_liftingRestrict_eq_of_cutVertex {G : Graph α β} {V₁ V₂ : Set α}
    {v : α} (hcover : V₁ ∪ V₂ = V(G)) (hoverlap : V₁ ∩ V₂ = {v})
    (hsep : ∀ e x y, G.IsLink e x y → (x ∈ V₁ ∧ y ∈ V₁) ∨ (x ∈ V₂ ∧ y ∈ V₂))
    {q : α × Fin 2 → K} {z₁ : α → K} (hz₁ : z₁ ∈ (G.induce V₁).liftingSpace q) :
    ∃ z ∈ G.liftingSpace q, Graph.liftingRestrict V₁ z = z₁ := by
  classical
  have hvV : v ∈ V₁ ∩ V₂ := hoverlap ▸ rfl
  obtain ⟨h, hh⟩ := hz₁.2 v hvV.1
  set z : α → K := fun w => if w ∈ V₁ then z₁ w else if w ∈ V₂ then h ⬝ᵥ pencilPicturePoint q w
    else 0 with hzdef
  -- `z` is the affine function `h` on `V₂`
  have hzV₂ : ∀ w ∈ V₂, z w = h ⬝ᵥ pencilPicturePoint q w := by
    intro w hw
    by_cases hw₁ : w ∈ V₁
    · have : w = v := by
        have : w ∈ V₁ ∩ V₂ := ⟨hw₁, hw⟩
        rwa [hoverlap] at this
      subst this
      simp only [hzdef, ite_eq_left hw₁]
      exact hh w (Or.inl rfl)
    · simp [hzdef, hw₁, hw]
  -- closed neighbourhoods of `G` off `v` stay on one side
  have hnbhd₁ : ∀ x ∈ V₁, ∀ w ∈ G.closedNbhd x, w ∈ V₂ → w ∉ V₁ → x = v := by
    intro x hx w hw hw₂ hw₁
    rcases hw with rfl | ⟨e, he⟩
    · exact absurd hx hw₁
    · rcases hsep e x w he with ⟨-, h'⟩ | ⟨hx₂, -⟩
      · exact absurd h' hw₁
      · have : x ∈ V₁ ∩ V₂ := ⟨hx, hx₂⟩
        rwa [hoverlap] at this
  refine ⟨z, ⟨fun w hw => ?_, fun x hx => ?_⟩, ?_⟩
  · have hw₁ : w ∉ V₁ := fun h' => hw (hcover ▸ Or.inl h')
    have hw₂ : w ∉ V₂ := fun h' => hw (hcover ▸ Or.inr h')
    simp [hzdef, hw₁, hw₂]
  · rw [← hcover] at hx
    by_cases hx₁ : x ∈ V₁
    · by_cases hxv : x = v
      · subst hxv
        refine ⟨h, fun w hw => ?_⟩
        by_cases hw₁ : w ∈ V₁
        · simp only [hzdef, ite_eq_left hw₁]
          refine hh w ?_
          rcases hw with rfl | ⟨e, he⟩
          · exact Or.inl rfl
          · exact Or.inr ⟨e, ⟨he, hx₁, hw₁⟩⟩
        · have hw₂ : w ∈ V₂ := by
            rcases hw with rfl | ⟨e, he⟩
            · exact absurd hx₁ hw₁
            · rcases hsep e x w he with ⟨-, h'⟩ | ⟨-, h'⟩
              · exact absurd h' hw₁
              · exact h'
          exact hzV₂ w hw₂
      · obtain ⟨h', hh'⟩ := hz₁.2 x hx₁
        refine ⟨h', fun w hw => ?_⟩
        have hw₁ : w ∈ V₁ := by
          by_contra hw₁
          have hw₂ : w ∈ V₂ := by
            rcases hw with rfl | ⟨e, he⟩
            · exact absurd hx₁ hw₁
            · rcases hsep e x w he with ⟨-, h''⟩ | ⟨-, h''⟩
              · exact absurd h'' hw₁
              · exact h''
          exact hxv (hnbhd₁ x hx₁ w hw hw₂ hw₁)
        simp only [hzdef, ite_eq_left hw₁]
        refine hh' w ?_
        rcases hw with rfl | ⟨e, he⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨e, ⟨he, hx₁, hw₁⟩⟩
    · have hx₂ : x ∈ V₂ := hx.resolve_left hx₁
      refine ⟨h, fun w hw => ?_⟩
      have hw₂ : w ∈ V₂ := by
        rcases hw with rfl | ⟨e, he⟩
        · exact hx₂
        · rcases hsep e x w he with ⟨h'', -⟩ | ⟨-, h''⟩
          · exact absurd h'' hx₁
          · exact h''
      exact hzV₂ w hw₂
  · funext w
    by_cases hw₁ : w ∈ V₁
    · simp [Graph.liftingRestrict_apply, hzdef, hw₁]
    · simp only [Graph.liftingRestrict_apply, ite_eq_right hw₁]
      exact (hz₁.1 w hw₁).symm

/-- **CUT** (`thm:pencil-x0-cut`; (MC-52)(iv), the half the induction uses): if `G` satisfies (H)
and has a cut vertex `v` splitting it into `G[V₁]` and `G[V₂]`, and `X₀` attains at both sides,
then `X₀(G)` attains. One picture `q` generic for both sides and main for `G`; heights
`z ∈ L_G(q)` whose two restrictions attain (the restrictions are onto, so each condition is a
nonzero polynomial on `L_G(q)`, and two such meet: `MvPolynomial.exists_mem_eval_ne_zero₂`); the
ranks add and the deficiencies glue, so `(q, z)` is a witness for `Graph.x0Attains_of_exists`. -/
theorem _root_.Graph.X0Attains.of_cutVertex [Infinite K] [Finite α] [Finite β] {G : Graph α β}
    (hG : G.IsX0Graph) {V₁ V₂ : Set α} {v : α} (hcover : V₁ ∪ V₂ = V(G))
    (hoverlap : V₁ ∩ V₂ = {v})
    (hsep : ∀ e x y, G.IsLink e x y → (x ∈ V₁ ∧ y ∈ V₁) ∨ (x ∈ V₂ ∧ y ∈ V₂))
    (h₁ : (G.induce V₁).X0Attains K) (h₂ : (G.induce V₂).X0Attains K) : G.X0Attains K := by
  classical
  have : Fintype α := Fintype.ofFinite α
  have hV : V(G).Nonempty := hG.connected.nonempty
  have : Inhabited α := ⟨hV.some⟩
  have hV₁ : V₁ ⊆ V(G) := hcover ▸ Set.subset_union_left
  have hV₂ : V₂ ⊆ V(G) := hcover ▸ Set.subset_union_right
  have hle₁ : G.induce V₁ ≤ G := Graph.induce_le hV₁
  have hle₂ : G.induce V₂ ≤ G := Graph.induce_le hV₂
  obtain ⟨ends₁, P₁, hends₁, hP₁, hgood₁⟩ := h₁
  obtain ⟨ends₂, P₂, hends₂, hP₂, hgood₂⟩ := h₂
  obtain ⟨Pm, hPm, hmain⟩ := G.exists_mvPolynomial_isMainPicture (K := K)
    hG.simple.toLoopless hG.three_le_ncard_closedNbhd
  set ends := G.endsOf with hendsdef
  have hends : ∀ e u w, G.IsLink e u w → G.IsLink e (ends e).1 (ends e).2 :=
    fun e _ _ he => G.isLink_endsOf he.edge_mem
  have hendsI : ∀ X : Set α, ∀ e u w, (G.induce X).IsLink e u w →
      (G.induce X).IsLink e (ends e).1 (ends e).2 := by
    intro X e u w he
    have hl := hends e u w he.1
    rcases hl.eq_and_eq_or_eq_and_eq he.1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨hl, h1 ▸ he.2.1, h2 ▸ he.2.2⟩
    · exact ⟨hl, h1 ▸ he.2.2, h2 ▸ he.2.1⟩
  obtain ⟨q, hq⟩ := MvPolynomial.exists_eval_ne_zero (mul_ne_zero (mul_ne_zero hP₁ hP₂) hPm)
  rw [map_mul, map_mul] at hq
  obtain ⟨-, R₁, ⟨z₁, hz₁, hR₁⟩, hatt₁⟩ := hgood₁ q (left_ne_zero_of_mul (left_ne_zero_of_mul hq))
  obtain ⟨-, R₂, ⟨z₂, hz₂, hR₂⟩, hatt₂⟩ := hgood₂ q (right_ne_zero_of_mul (left_ne_zero_of_mul hq))
  have hqmain := hmain q (right_ne_zero_of_mul hq)
  -- each restriction condition is nonzero somewhere on `L_G(q)`
  have hex₁ : ∃ z ∈ G.liftingSpace q, MvPolynomial.eval z (restrictPoly V₁ R₁) ≠ 0 := by
    obtain ⟨z, hz, hzr⟩ := Graph.exists_liftingRestrict_eq_of_cutVertex hcover hoverlap hsep hz₁
    exact ⟨z, hz, by rwa [eval_restrictPoly, hzr]⟩
  have hex₂ : ∃ z ∈ G.liftingSpace q, MvPolynomial.eval z (restrictPoly V₂ R₂) ≠ 0 := by
    have hcover' : V₂ ∪ V₁ = V(G) := by rw [Set.union_comm]; exact hcover
    have hoverlap' : V₂ ∩ V₁ = {v} := by rw [Set.inter_comm]; exact hoverlap
    have hsep' : ∀ e x y, G.IsLink e x y → (x ∈ V₂ ∧ y ∈ V₂) ∨ (x ∈ V₁ ∧ y ∈ V₁) :=
      fun e x y he => (hsep e x y he).symm
    obtain ⟨z, hz, hzr⟩ := Graph.exists_liftingRestrict_eq_of_cutVertex hcover' hoverlap' hsep' hz₂
    exact ⟨z, hz, by rwa [eval_restrictPoly, hzr]⟩
  obtain ⟨z, hz, hz₁', hz₂'⟩ := MvPolynomial.exists_mem_eval_ne_zero₂ hex₁ hex₂
  rw [eval_restrictPoly] at hz₁' hz₂'
  have hr₁ := hatt₁ _ (Graph.liftingRestrict_mem_liftingSpace hle₁ hz) hz₁'
  have hr₂ := hatt₂ _ (Graph.liftingRestrict_mem_liftingSpace hle₂ hz) hz₂'
  -- carry each side's rank to the selector `ends` and the unrestricted heights
  have hcongr : ∀ (X : Set α) (endsX : β → α × α),
      (∀ e u w, (G.induce X).IsLink e u w → (G.induce X).IsLink e (endsX e).1 (endsX e).2) →
      Module.finrank K (Submodule.span K (PanelHingeFramework.ofNormals (k := 2) (G.induce X)
          endsX (fun p => pencilConfigPoint q (Graph.liftingRestrict X z) p.1 p.2)
            ).toBodyHinge.rigidityRows)
        = Module.finrank K (Submodule.span K (PanelHingeFramework.ofNormals (k := 2) (G.induce X)
          ends (fun p => pencilConfigPoint q z p.1 p.2)).toBodyHinge.rigidityRows) := by
    intro X endsX hendsX
    refine PanelHingeFramework.finrank_span_rigidityRows_ofNormals_congr _ hendsX (hendsI X) ?_
    intro x hx i
    exact pencilConfigPoint_liftingRestrict X q z hx i
  rw [show V(G.induce V₁) = V₁ from rfl] at hr₁
  rw [show V(G.induce V₂) = V₂ from rfl] at hr₂
  rw [hcongr V₁ ends₁ hends₁] at hr₁
  rw [hcongr V₂ ends₂ hends₂] at hr₂
  -- the ranks add
  have hadd := BodyHingeFramework.finrank_span_rigidityRows_cutVertex_eq
    (PanelHingeFramework.ofNormals (k := 2) G ends
      (fun p => pencilConfigPoint q z p.1 p.2)).toBodyHinge (v := v) hoverlap.le hsep
  -- the deficiencies glue, and the body counts overlap in one
  have hdef := Graph.deficiency_add_le_of_cutVertex hG.simple.toLoopless 3 hcover hoverlap hsep
  have hcount : (V₁.ncard : ℤ) + V₂.ncard = V(G).ncard + 1 := by
    have := Set.ncard_union_add_ncard_inter V₁ V₂ (Set.toFinite _) (Set.toFinite _)
    rw [hcover, hoverlap, Set.ncard_singleton] at this
    exact_mod_cast this.symm
  refine Graph.x0Attains_of_exists hV ends hends hqmain hz ?_
  have e1 : (Module.finrank K (Submodule.span K (PanelHingeFramework.ofNormals (k := 2) G ends
      (fun p => pencilConfigPoint q z p.1 p.2)).toBodyHinge.rigidityRows) : ℤ)
      = (Module.finrank K (Submodule.span K (PanelHingeFramework.ofNormals (k := 2) (G.induce V₁)
          ends (fun p => pencilConfigPoint q z p.1 p.2)).toBodyHinge.rigidityRows) : ℤ)
        + (Module.finrank K (Submodule.span K (PanelHingeFramework.ofNormals (k := 2)
          (G.induce V₂) ends (fun p => pencilConfigPoint q z p.1 p.2)).toBodyHinge.rigidityRows)
            : ℤ) := by
    exact_mod_cast hadd
  rw [e1, hr₁, hr₂, show screwDim 2 = 6 from rfl]
  push_cast
  linarith [hdef, hcount]

/-! ## A single bridge

The `k = 0` case of (MC-53), kept as build 2's base case (`notes/Phase40e.md`). -/

/-- Prescribed values on two independent vectors of `K³` are taken by one linear functional,
written as a dot product. -/
theorem exists_dotProduct_eq_of_linearIndependent {u w : Fin 3 → K}
    (h : LinearIndependent K ![u, w]) (c₁ c₂ : K) :
    ∃ γ : Fin 3 → K, γ ⬝ᵥ u = c₁ ∧ γ ⬝ᵥ w = c₂ := by
  classical
  set T := Fintype.linearCombination K ![u, w] with hT
  have hinj : LinearMap.ker T = ⊥ :=
    LinearMap.ker_eq_bot.mpr (linearIndependent_iff_injective_fintypeLinearCombination.mp h)
  obtain ⟨L, hL⟩ := T.exists_leftInverse_of_injective hinj
  set φ : (Fin 3 → K) →ₗ[K] K :=
    (LinearMap.proj 0 : (Fin 2 → K) →ₗ[K] K).smulRight c₁ ∘ₗ L
      + (LinearMap.proj 1 : (Fin 2 → K) →ₗ[K] K).smulRight c₂ ∘ₗ L with hφ
  have hφdot : ∀ x, (fun i => φ (Pi.single i 1)) ⬝ᵥ x = φ x := by
    intro x
    conv_rhs => rw [show x = ∑ i, x i • Pi.single i (1 : K) by
      funext j; simp [Finset.sum_apply, Pi.single_apply]]
    rw [map_sum]
    simp [dotProduct, mul_comm]
  have hLu : L u = Pi.single 0 1 := by
    have := congr($hL (Pi.single 0 1))
    simpa [hT, Fintype.linearCombination_apply_single] using this
  have hLw : L w = Pi.single 1 1 := by
    have := congr($hL (Pi.single 1 1))
    simpa [hT, Fintype.linearCombination_apply_single] using this
  refine ⟨fun i => φ (Pi.single i 1), ?_, ?_⟩
  · rw [hφdot, hφ]; simp [hLu]
  · rw [hφdot, hφ]; simp [hLw]

/-- **Restriction is onto at a single bridge** ((MC-53)(iii) with no path bodies): the bridge
`e = ab` joins `a ∈ V₁` to `b ∉ V₁`, every other link stays on one side, and `q_a ≠ q_b`. Extend
`z₁ ∈ L_{G[V₁]}(q)` across the other side by an affine function taking the value `z₁(a)` at `q_a`
and the value of `z₁`'s plane at `a` at `q_b`. -/
theorem _root_.Graph.exists_liftingRestrict_eq_of_bridge {G : Graph α β} {V₁ : Set α}
    (hsub : V₁ ⊆ V(G)) {e : β} {a b : α} (ha : a ∈ V₁) (hb : b ∉ V₁) (hl : G.IsLink e a b)
    (hsep : ∀ f x y, G.IsLink f x y → f ≠ e →
      (x ∈ V₁ ∧ y ∈ V₁) ∨ (x ∉ V₁ ∧ y ∉ V₁))
    {q : α × Fin 2 → K} (hab : pencilPicturePoint q a ≠ pencilPicturePoint q b)
    {z₁ : α → K} (hz₁ : z₁ ∈ (G.induce V₁).liftingSpace q) :
    ∃ z ∈ G.liftingSpace q, Graph.liftingRestrict V₁ z = z₁ := by
  classical
  obtain ⟨h₁, hh₁⟩ := hz₁.2 a ha
  obtain ⟨γ, hγa, hγb⟩ := exists_dotProduct_eq_of_linearIndependent
    (linearIndependent_pencilPicturePoint_pair hab) (z₁ a) (h₁ ⬝ᵥ pencilPicturePoint q b)
  set z : α → K := fun w => if w ∈ V₁ then z₁ w else if w ∈ V(G) then γ ⬝ᵥ pencilPicturePoint q w
    else 0 with hzdef
  -- a link leaving `V₁` is the bridge
  have hcross : ∀ f x y, G.IsLink f x y → x ∈ V₁ → y ∉ V₁ → x = a ∧ y = b := by
    intro f x y hf hx hy
    by_cases hfe : f = e
    · subst hfe
      rcases hf.eq_and_eq_or_eq_and_eq hl with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨h1, h2⟩
      · exact absurd (h2 ▸ ha) hy
    · rcases hsep f x y hf hfe with ⟨-, h'⟩ | ⟨h', -⟩
      · exact absurd h' hy
      · exact absurd hx h'
  refine ⟨z, ⟨fun w hw => ?_, fun x hx => ?_⟩, ?_⟩
  · have hw₁ : w ∉ V₁ := fun h' => hw (hsub h')
    simp [hzdef, hw₁, hw]
  · by_cases hx₁ : x ∈ V₁
    · by_cases hxa : x = a
      · subst hxa
        refine ⟨h₁, fun w hw => ?_⟩
        by_cases hw₁ : w ∈ V₁
        · simp only [hzdef, ite_eq_left hw₁]
          refine hh₁ w ?_
          rcases hw with rfl | ⟨f, hf⟩
          · exact Or.inl rfl
          · exact Or.inr ⟨f, ⟨hf, hx₁, hw₁⟩⟩
        · rcases hw with rfl | ⟨f, hf⟩
          · exact absurd hx₁ hw₁
          obtain ⟨-, rfl⟩ := hcross f x w hf hx₁ hw₁
          have hwV : w ∈ V(G) := hf.right_mem
          simp only [hzdef, ite_eq_right hw₁, ite_eq_left hwV]
          exact hγb
      · obtain ⟨h, hh⟩ := hz₁.2 x hx₁
        refine ⟨h, fun w hw => ?_⟩
        have hw₁ : w ∈ V₁ := by
          by_contra hw₁
          rcases hw with rfl | ⟨f, hf⟩
          · exact hw₁ hx₁
          · exact hxa (hcross f x w hf hx₁ hw₁).1
        simp only [hzdef, ite_eq_left hw₁]
        refine hh w ?_
        rcases hw with rfl | ⟨f, hf⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨f, ⟨hf, hx₁, hw₁⟩⟩
    · refine ⟨γ, fun w hw => ?_⟩
      by_cases hw₁ : w ∈ V₁
      · rcases hw with rfl | ⟨f, hf⟩
        · exact absurd hw₁ hx₁
        obtain ⟨rfl, rfl⟩ := hcross f w x hf.symm hw₁ hx₁
        simp only [hzdef, ite_eq_left hw₁]
        exact hγa.symm
      · have hwV : w ∈ V(G) := by
          rcases hw with rfl | ⟨f, hf⟩
          · exact hx
          · exact hf.right_mem
        simp [hzdef, hw₁, hwV]
  · funext w
    by_cases hw₁ : w ∈ V₁
    · simp [Graph.liftingRestrict_apply, hzdef, hw₁]
    · simp only [Graph.liftingRestrict_apply, ite_eq_right hw₁]
      exact (hz₁.1 w hw₁).symm

/-- **BRIDGE at a single bridge** ((MC-53)(iv) with no path bodies, the "if" half): if `G`
satisfies (H), the bridge `e` joins `a ∈ V₁` to `b ∉ V₁` and every other link stays on one side,
and `X₀` attains at both sides, then `X₀(G)` attains. The landed pieces: the cut-edge rank brick
`BodyHingeFramework.le_finrank_span_rigidityRows_of_cut` (ranks add plus `5` for the bridge) and
KT Lemma 3.6 `Graph.deficiency_eq_of_cutEdges_ncard_le_one` (the deficiency adds plus `1`). -/
theorem _root_.Graph.X0Attains.of_bridge [Infinite K] [Finite α] [Finite β] {G : Graph α β}
    (hG : G.IsX0Graph) {V₁ : Set α} (hne : V₁.Nonempty) (hssub : V₁ ⊂ V(G)) {e : β} {a b : α}
    (ha : a ∈ V₁) (hb : b ∉ V₁) (hl : G.IsLink e a b)
    (hsep : ∀ f x y, G.IsLink f x y → f ≠ e → (x ∈ V₁ ∧ y ∈ V₁) ∨ (x ∉ V₁ ∧ y ∉ V₁))
    (h₁ : (G.induce V₁).X0Attains K) (h₂ : (G.induce (V(G) \ V₁)).X0Attains K) :
    G.X0Attains K := by
  classical
  have : Fintype α := Fintype.ofFinite α
  have hV : V(G).Nonempty := hG.connected.nonempty
  have : Inhabited α := ⟨hV.some⟩
  have hsub : V₁ ⊆ V(G) := hssub.subset
  set V₂ := V(G) \ V₁ with hV₂
  have hle₁ : G.induce V₁ ≤ G := Graph.induce_le hsub
  have hle₂ : G.induce V₂ ≤ G := Graph.induce_le Set.sdiff_subset
  obtain ⟨ends₁, P₁, hends₁, hP₁, hgood₁⟩ := h₁
  obtain ⟨ends₂, P₂, hends₂, hP₂, hgood₂⟩ := h₂
  obtain ⟨Pm, hPm, hmain⟩ := G.exists_mvPolynomial_isMainPicture (K := K)
    hG.simple.toLoopless hG.three_le_ncard_closedNbhd
  set ends := G.endsOf with hendsdef
  have hends : ∀ f u w, G.IsLink f u w → G.IsLink f (ends f).1 (ends f).2 :=
    fun f _ _ hf => G.isLink_endsOf hf.edge_mem
  have hendsI : ∀ X : Set α, ∀ f u w, (G.induce X).IsLink f u w →
      (G.induce X).IsLink f (ends f).1 (ends f).2 := by
    intro X f u w hf
    have hl' := hends f u w hf.1
    rcases hl'.eq_and_eq_or_eq_and_eq hf.1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨hl', h1 ▸ hf.2.1, h2 ▸ hf.2.2⟩
    · exact ⟨hl', h1 ▸ hf.2.2, h2 ▸ hf.2.1⟩
  obtain ⟨q, hq⟩ := MvPolynomial.exists_eval_ne_zero (mul_ne_zero (mul_ne_zero hP₁ hP₂) hPm)
  rw [map_mul, map_mul] at hq
  obtain ⟨-, R₁, ⟨z₁, hz₁, hR₁⟩, hatt₁⟩ := hgood₁ q (left_ne_zero_of_mul (left_ne_zero_of_mul hq))
  obtain ⟨-, R₂, ⟨z₂, hz₂, hR₂⟩, hatt₂⟩ := hgood₂ q (right_ne_zero_of_mul (left_ne_zero_of_mul hq))
  have hqmain := hmain q (right_ne_zero_of_mul hq)
  have hab : pencilPicturePoint q a ≠ pencilPicturePoint q b := hqmain.1.1 e a b hl
  have hbV : b ∈ V₂ := ⟨hl.right_mem, hb⟩
  have haV₂ : a ∉ V₂ := fun h => h.2 ha
  have hsep₂ : ∀ f x y, G.IsLink f x y → f ≠ e → (x ∈ V₂ ∧ y ∈ V₂) ∨ (x ∉ V₂ ∧ y ∉ V₂) := by
    intro f x y hf hfe
    rcases hsep f x y hf hfe with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · exact Or.inr ⟨fun h => h.2 hx, fun h => h.2 hy⟩
    · exact Or.inl ⟨⟨hf.left_mem, hx⟩, ⟨hf.right_mem, hy⟩⟩
  have hex₁ : ∃ z ∈ G.liftingSpace q, MvPolynomial.eval z (restrictPoly V₁ R₁) ≠ 0 := by
    obtain ⟨z, hz, hzr⟩ := Graph.exists_liftingRestrict_eq_of_bridge hsub ha hb hl hsep hab hz₁
    exact ⟨z, hz, by rwa [eval_restrictPoly, hzr]⟩
  have hex₂ : ∃ z ∈ G.liftingSpace q, MvPolynomial.eval z (restrictPoly V₂ R₂) ≠ 0 := by
    obtain ⟨z, hz, hzr⟩ := Graph.exists_liftingRestrict_eq_of_bridge Set.sdiff_subset hbV haV₂
      hl.symm hsep₂ hab.symm hz₂
    exact ⟨z, hz, by rwa [eval_restrictPoly, hzr]⟩
  obtain ⟨z, hz, hz₁', hz₂'⟩ := MvPolynomial.exists_mem_eval_ne_zero₂ hex₁ hex₂
  rw [eval_restrictPoly] at hz₁' hz₂'
  have hr₁ := hatt₁ _ (Graph.liftingRestrict_mem_liftingSpace hle₁ hz) hz₁'
  have hr₂ := hatt₂ _ (Graph.liftingRestrict_mem_liftingSpace hle₂ hz) hz₂'
  have hcongr : ∀ (X : Set α) (endsX : β → α × α),
      (∀ f u w, (G.induce X).IsLink f u w → (G.induce X).IsLink f (endsX f).1 (endsX f).2) →
      Module.finrank K (Submodule.span K (PanelHingeFramework.ofNormals (k := 2) (G.induce X)
          endsX (fun p => pencilConfigPoint q (Graph.liftingRestrict X z) p.1 p.2)
            ).toBodyHinge.rigidityRows)
        = Module.finrank K (Submodule.span K (PanelHingeFramework.ofNormals (k := 2) (G.induce X)
          ends (fun p => pencilConfigPoint q z p.1 p.2)).toBodyHinge.rigidityRows) := by
    intro X endsX hendsX
    refine PanelHingeFramework.finrank_span_rigidityRows_ofNormals_congr _ hendsX (hendsI X) ?_
    intro x hx i
    exact pencilConfigPoint_liftingRestrict X q z hx i
  rw [show V(G.induce V₁) = V₁ from rfl] at hr₁
  rw [show V(G.induce V₂) = V₂ from rfl] at hr₂
  rw [hcongr V₁ ends₁ hends₁] at hr₁
  rw [hcongr V₂ ends₂ hends₂] at hr₂
  -- the cut is the bridge
  have hcut : G.cutEdges V₁ = {e} := by
    ext f
    simp only [Graph.cutEdges, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨-, x, y, hf, hx, hy⟩
      by_contra hfe
      rcases hsep f x y hf hfe with ⟨-, h'⟩ | ⟨h', -⟩
      · exact hy h'
      · exact h' hx
    · rintro rfl
      exact ⟨hl.edge_mem, a, b, hl, ha, hb⟩
  -- the ranks add, plus the bridge's `5`
  have hbrick := BodyHingeFramework.le_finrank_span_rigidityRows_of_cut
    (PanelHingeFramework.ofNormals (k := 2) G ends
      (fun p => pencilConfigPoint q z p.1 p.2)).toBodyHinge (V₁ := V₁) (C := {e})
    (by simp) (fun f u w hf => hqmain.1.supportExtensor_ne_zero hends z hf)
    (fun f u w hf hfC => hsep f u w hf (by simpa using hfC))
    (fun f hf => by rw [Set.mem_singleton_iff.mp hf]; exact ⟨a, b, hl, ha, hb⟩)
  -- the deficiency adds, plus `1`
  have hdef := Graph.deficiency_eq_of_cutEdges_ncard_le_one (n := 3) (by decide) hne hssub
    (by rw [hcut, Set.ncard_singleton])
  rw [hcut, Set.ncard_singleton] at hdef
  have hcount : (V₁.ncard : ℤ) + V₂.ncard = V(G).ncard := by
    have := Set.ncard_sdiff_add_ncard_of_subset hsub (Set.toFinite _)
    rw [← hV₂] at this
    exact_mod_cast (by omega : V₁.ncard + V₂.ncard = V(G).ncard)
  refine Graph.x0Attains_of_exists hV ends hends hqmain hz ?_
  have e1 : (Module.finrank K (Submodule.span K (PanelHingeFramework.ofNormals (k := 2)
        (G.induce V₁) ends (fun p => pencilConfigPoint q z p.1 p.2)).toBodyHinge.rigidityRows)
          : ℤ)
      + (screwDim 2 - 1) * 1
      + (Module.finrank K (Submodule.span K (PanelHingeFramework.ofNormals (k := 2)
          (G.induce V₂) ends (fun p => pencilConfigPoint q z p.1 p.2)).toBodyHinge.rigidityRows)
            : ℤ)
      ≤ (Module.finrank K (Submodule.span K (PanelHingeFramework.ofNormals (k := 2) G ends
          (fun p => pencilConfigPoint q z p.1 p.2)).toBodyHinge.rigidityRows) : ℤ) := by
    have := hbrick
    simp only [Set.ncard_singleton] at this
    exact_mod_cast this
  rw [hr₁, hr₂, show screwDim 2 = 6 from rfl] at e1
  rw [show screwDim 2 = 6 from rfl, hdef]
  have hb3 : (Graph.bodyBarDim 3 : ℤ) = 6 := rfl
  rw [hb3]
  push_cast at e1 ⊢
  linarith [hcount]

/-! ## A chain of bridges

Build 2, BRIDGE for every `k` (`notes/Phase40e.md`). Explicit path hypotheses, not a chain
structure (the PI-endorsed plan, *Architectural choices*): the path's interior bodies are an
injective `x : Fin k → α`, and `pathVertex a x b : Fin (k + 2) → α` is the extended sequence
`a, x 0, …, x (k - 1), b` its `k + 1` edges link in order. -/

/-- **The path's extended vertex sequence** (Phase 40e BRIDGE): `a`, the interior bodies
`x 0, …, x (k - 1)`, then `b`, as one `Fin (k + 2) → α`. -/
def pathVertex {k : ℕ} (a : α) (x : Fin k → α) (b : α) : Fin (k + 2) → α :=
  Fin.snoc (Fin.cons a x) b

@[simp] theorem pathVertex_zero {k : ℕ} (a : α) (x : Fin k → α) (b : α) :
    pathVertex a x b 0 = a := by
  simp [pathVertex]

/-- **Every non-initial member of the path sequence is `b` or an interior body** (Phase 40e
BRIDGE): the only index `pathVertex` sends to `a` is `0` (`pathVertex_zero`), so a nonzero index
lands on `b` (the last position) or on some `x i` (an interior position). -/
theorem pathVertex_eq_or_exists {k : ℕ} (a : α) (x : Fin k → α) (b : α)
    {j : Fin (k + 2)} (hj : j ≠ 0) :
    pathVertex a x b j = b ∨ ∃ i, pathVertex a x b j = x i := by
  induction j using Fin.lastCases with
  | last => exact Or.inl (by simp [pathVertex])
  | cast i =>
    refine Or.inr ?_
    rw [pathVertex, Fin.snoc_castSucc]
    induction i using Fin.cases with
    | zero => exact absurd rfl hj
    | succ i' => exact ⟨i', by simp⟩

/-- **Restriction is onto at a chain of bridges** (`lem:pencil-bridge-fibre`; (MC-53)(iii)): the
path `a - x 0 - ⋯ - x (k - 1) - b` (`hpath`, along `pathVertex`) joins `a ∈ V₁` to `b ∉ V₁`, and
every other link of `G` stays on one side (`hsep`). Extend `z₁ ∈ L_{G[V₁]}(q)` across the rest of
`G` by the same affine function `h₁` that already witnesses `z₁`'s own closed-neighbourhood
condition at `a`: `a` is the only body of `V₁` with an edge leaving `V₁` (`hgate`, read off
`hpath`/`hsep` — the only path edge that can touch `V₁` is the first, and only at `a`, since every
other member of the path sequence is `b` or an interior body, `pathVertex_eq_or_exists`), so every
closed neighbourhood outside `V₁` either lies entirely there or meets `V₁` only at `a`, where `h₁`
already agrees with `z₁`. No admissibility of `q` and no case split on `k` is needed. -/
theorem _root_.Graph.exists_liftingRestrict_eq_of_bridgePath {G : Graph α β} {V₁ : Set α}
    (hsub : V₁ ⊆ V(G)) {k : ℕ} {x : Fin k → α} (hxV₁ : ∀ i, x i ∉ V₁)
    {a b : α} (ha : a ∈ V₁) (hb : b ∉ V₁)
    {e : Fin (k + 1) → β}
    (hpath : ∀ i : Fin (k + 1),
      G.IsLink (e i) (pathVertex a x b i.castSucc) (pathVertex a x b i.succ))
    (hsep : ∀ f u v, G.IsLink f u v → (∀ i, f ≠ e i) →
      (u ∈ V₁ ∧ v ∈ V₁) ∨ (u ∉ V₁ ∧ v ∉ V₁))
    {q : α × Fin 2 → K} {z₁ : α → K} (hz₁ : z₁ ∈ (G.induce V₁).liftingSpace q) :
    ∃ z ∈ G.liftingSpace q, Graph.liftingRestrict V₁ z = z₁ := by
  classical
  have hgate : ∀ f u v, G.IsLink f u v → u ∈ V₁ → v ∉ V₁ → u = a := by
    intro f u v hl hu hv
    by_cases hcase : ∃ i, f = e i
    · obtain ⟨i0, rfl⟩ := hcase
      have hl0 := hpath i0
      rcases hl.eq_and_eq_or_eq_and_eq hl0 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · by_cases hi0 : i0 = 0
        · subst hi0; simp
        · exfalso
          have hne : pathVertex a x b i0.castSucc ∉ V₁ := by
            rcases pathVertex_eq_or_exists a x b (j := i0.castSucc)
              (by simpa [Fin.castSucc_eq_zero_iff] using hi0) with h | ⟨i, h⟩
            · rw [h]; exact hb
            · rw [h]; exact hxV₁ i
          exact hne hu
      · exfalso
        have hnz : i0.succ ≠ 0 := Fin.succ_ne_zero i0
        have hne : pathVertex a x b i0.succ ∉ V₁ := by
          rcases pathVertex_eq_or_exists a x b (j := i0.succ) hnz with h | ⟨i, h⟩
          · rw [h]; exact hb
          · rw [h]; exact hxV₁ i
        exact hne hu
    · have hcase' : ∀ i, f ≠ e i := fun i hfi => hcase ⟨i, hfi⟩
      rcases hsep f u v hl hcase' with ⟨-, hv1⟩ | ⟨hu2, -⟩
      · exact absurd hv1 hv
      · exact absurd hu hu2
  obtain ⟨h₁, hh₁⟩ := hz₁.2 a ha
  set z : α → K := fun w => if w ∈ V₁ then z₁ w
    else if w ∈ V(G) then h₁ ⬝ᵥ pencilPicturePoint q w else 0 with hzdef
  have haa : z₁ a = h₁ ⬝ᵥ pencilPicturePoint q a := hh₁ a (Or.inl rfl)
  refine ⟨z, ⟨fun w hw => ?_, fun v hv => ?_⟩, ?_⟩
  · have hw₁ : w ∉ V₁ := fun h => hw (hsub h)
    simp [hzdef, hw₁, hw]
  · by_cases hv1 : v ∈ V₁
    · by_cases hva : v = a
      · subst hva
        refine ⟨h₁, fun w hw => ?_⟩
        by_cases hw1 : w ∈ V₁
        · simp only [hzdef, ite_eq_left hw1]
          refine hh₁ w ?_
          rcases hw with rfl | ⟨f, hf⟩
          · exact Or.inl rfl
          · exact Or.inr ⟨f, ⟨hf, hv1, hw1⟩⟩
        · have hwV : w ∈ V(G) := by
            rcases hw with rfl | ⟨f, hf⟩
            · exact hv
            · exact hf.right_mem
          simp only [hzdef, ite_eq_right hw1, ite_eq_left hwV]
      · obtain ⟨h, hh⟩ := hz₁.2 v hv1
        refine ⟨h, fun w hw => ?_⟩
        have hw1 : w ∈ V₁ := by
          by_contra hw1
          rcases hw with rfl | ⟨f, hf⟩
          · exact hw1 hv1
          · exact hva (hgate f v w hf hv1 hw1)
        simp only [hzdef, ite_eq_left hw1]
        refine hh w ?_
        rcases hw with rfl | ⟨f, hf⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨f, ⟨hf, hv1, hw1⟩⟩
    · refine ⟨h₁, fun w hw => ?_⟩
      by_cases hw1 : w ∈ V₁
      · rcases hw with rfl | ⟨f, hf⟩
        · exact absurd hw1 hv1
        have hwa : w = a := hgate f w v hf.symm hw1 hv1
        subst hwa
        simp only [hzdef, ite_eq_left hw1]
        exact haa
      · have hwV : w ∈ V(G) := by
          rcases hw with rfl | ⟨f, hf⟩
          · exact hv
          · exact hf.right_mem
        simp [hzdef, hw1, hwV]
  · funext w
    by_cases hw1 : w ∈ V₁
    · simp [Graph.liftingRestrict_apply, hzdef, hw1]
    · simp only [Graph.liftingRestrict_apply, ite_eq_right hw1]
      exact (hz₁.1 w hw1).symm

end CombinatorialRigidity.Molecular
