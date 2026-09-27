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
* `Graph.IsAdmissiblePicture.exists_dotProduct_of_ncard_closedNbhd_le_three` — three points impose
  nothing: at an admissible picture a closed neighbourhood with at most three members carries every
  height affinely (`lem:pencil-three-points`, Phase 40g; the ear steps' free interior bodies).
* `Graph.liftingRestrict`, `Graph.liftingRestrict_mem_liftingSpace`,
  `pencilConfigPoint_liftingRestrict` — a height restricted to a subgraph's bodies is a height of
  the subgraph, with the same configuration points there; `restrictPoly` / `eval_restrictPoly`
  read a polynomial in the heights on the restriction.
* `Graph.exists_liftingRestrict_eq_of_cutVertex` — at a cut vertex the restriction is onto, at
  every picture ((MC-52)(iii)).
* `Graph.X0Attains.of_cutVertex` — **CUT** ((MC-52)(iv), the "if" half), from the rank identity
  `BodyHingeFramework.finrank_span_rigidityRows_cutVertex_eq` (`RigidityMatrix/Bricks.lean`) and
  the deficiency law `Graph.deficiency_add_le_of_cutVertex` (`Molecular/Deficiency.lean`).
* `pathVertex` — the path's extended vertex sequence `a, x 0, …, x (k - 1), b`.
* `Graph.exists_liftingRestrict_eq_of_bridgePath` — restriction is onto at a chain of bridges of
  any length `k` ((MC-53)(iii), `lem:pencil-bridge-fibre`): a single affine extension by the
  witness at `a`, needing no admissibility of the picture and no case split on `k`.
* `pathVertex_cases`, `pathVertex_eq_of_val_eq_succ`, `pathVertex_rev`,
  `pathVertex_mem_union_image_iff` — the path sequence read by index value, read backwards, and
  against the prefixes `V₁ ∪ {x i | i < j}`; `pathVertex_last`, `pathVertex_injective`,
  `pathVertex_val_succ`, `pathVertex_eq_x_iff`, `pathVertex_shift` and `image_val_lt_eq_range`
  serve the ear steps (`MainComponent/Ear.lean`, `MainComponent/Chain.lean`, Phase 40g).
* `Graph.cutEdges_union_image_of_bridgePath`, `Graph.deficiency_induce_union_range_of_bridgePath`,
  `BodyHingeFramework.add_le_finrank_span_rigidityRows_induce_union_range_of_bridgePath` — the
  counts along the path: each body hangs from the prefix before it by one edge, so it adds `1` to
  the deficiency and at least `D − 1` to the rank.
* `Graph.X0Attains.of_bridgePath` — **BRIDGE** ((MC-53)(iv), the "if" half) at a chain of `k + 1`
  bridges, any `k ≥ 0`: the cut-edge rank brick
  `BodyHingeFramework.le_finrank_span_rigidityRows_of_cut` and KT Lemma 3.6
  `Graph.deficiency_eq_of_cutEdges_ncard_le_one` at the last bridge, plus the counts along the
  path. The rank step is the pendant-body brick
  `BodyHingeFramework.add_le_finrank_span_rigidityRows_induce_union_singleton`
  (`RigidityMatrix/Bricks.lean`), the deficiency step `Graph.deficiency_induce_union_singleton`
  (`Molecule/Pencil/Motive.lean`).

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
  admissibility are never used for this direction, and no case split on `k` is needed. The lemma
  stays minimal (no `V₂`, no exact vertex count, no injectivity of `x`); the theorem adds those,
  which its rank and deficiency counts need.
* **BRIDGE counts in numbers, not by an induction on `X0Attains`.** A peeled path body has no
  admissible picture (its closed neighbourhood is itself), so no intermediate graph attains. The
  theorem cuts once at the last bridge and telescopes the rank inequality and the deficiency
  equality along the path, then applies `Graph.x0Attains_of_exists` once. The single bridge is its
  `k = 0` case.
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

/-! ## Three points impose nothing -/

/-- **Three points impose nothing** (Phase 40g CHAIN, `lem:pencil-three-points`; the no-hub half
of (MC-21)(a)'s `L = K^V`): at an admissible picture, a closed neighbourhood with at most three
members carries every height affinely. Admissibility gives three members with independent picture
points, which are then all of it, and the heights there are matched by the inverse of the matrix
of those points. -/
theorem _root_.Graph.IsAdmissiblePicture.exists_dotProduct_of_ncard_closedNbhd_le_three
    [Finite α] {G : Graph α β} {q : α × Fin 2 → K} (hq : G.IsAdmissiblePicture q) {v : α}
    (hv : v ∈ V(G)) (h3 : (G.closedNbhd v).ncard ≤ 3) (z : α → K) :
    ∃ h : Fin 3 → K, ∀ w ∈ G.closedNbhd v, z w = h ⬝ᵥ pencilPicturePoint q w := by
  classical
  obtain ⟨t, ht, hli⟩ := hq.2 v hv
  have htinj : Function.Injective t := fun i j hij => hli.injective (by simp [hij])
  have hrange : Set.range t = G.closedNbhd v := by
    refine Set.eq_of_subset_of_ncard_le (by rintro _ ⟨i, rfl⟩; exact ht i) ?_ (Set.toFinite _)
    rw [Set.ncard_range_of_injective htinj, Nat.card_eq_fintype_card, Fintype.card_fin]
    exact h3
  set M : Matrix (Fin 3) (Fin 3) K := Matrix.of fun i => pencilPicturePoint q (t i) with hM
  have hunit : IsUnit M := Matrix.linearIndependent_rows_iff_isUnit.mp hli
  refine ⟨Matrix.mulVec M⁻¹ (fun i => z (t i)), fun w hw => ?_⟩
  rw [← hrange] at hw
  obtain ⟨i, rfl⟩ := hw
  have hMM : M.mulVec (Matrix.mulVec M⁻¹ (fun i => z (t i))) = fun i => z (t i) := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det M).mp hunit),
      Matrix.one_mulVec]
  have := congr_fun hMM i
  rw [← this, dotProduct_comm]
  rfl

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

/-- **The path sequence ends at `b`** (Phase 40g CHAIN): the last index `k + 1` is sent to `b`. -/
theorem pathVertex_last {k : ℕ} (a : α) (x : Fin k → α) (b : α) :
    pathVertex a x b (Fin.last (k + 1)) = b := by
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

/-! ## A chain of bridges: the counts, and BRIDGE

The theorem computes the rank inequality and the deficiency equality as numbers along the path,
never forming an intermediate `X0Attains` claim: a peeled path body has no admissible picture
(its closed neighbourhood in the peeled graph is itself). It cuts once at the last bridge, whose
far side is `V₂`, and telescopes over the prefixes `V₁ ∪ {x i | i < j}` of the path, each of which
the next body `x j` hangs from by the single edge `e j`. -/

/-- **The three kinds of position in the path sequence** (Phase 40e BRIDGE): index `0` is `a`, an
index of value `i + 1` is the interior body `x i`, and index `k + 1` is `b`. Read off by value, so
index arithmetic goes to `omega`. -/
theorem pathVertex_cases {k : ℕ} (a : α) (x : Fin k → α) (b : α) (m : Fin (k + 2)) :
    (m.val = 0 ∧ pathVertex a x b m = a) ∨
      (∃ i : Fin k, m.val = i.val + 1 ∧ pathVertex a x b m = x i) ∨
      (m.val = k + 1 ∧ pathVertex a x b m = b) := by
  induction m using Fin.lastCases with
  | last => exact Or.inr (Or.inr ⟨by simp, by simp [pathVertex]⟩)
  | cast i =>
    rw [pathVertex, Fin.snoc_castSucc]
    induction i using Fin.cases with
    | zero => exact Or.inl ⟨by simp, by simp⟩
    | succ i' => exact Or.inr (Or.inl ⟨i', by simp, by simp⟩)

/-- **An interior position, by value** (Phase 40e BRIDGE): an index of value `i + 1` is sent to
the interior body `x i`. -/
theorem pathVertex_eq_of_val_eq_succ {k : ℕ} (a : α) (x : Fin k → α) (b : α) {m : Fin (k + 2)}
    {i : Fin k} (h : m.val = i.val + 1) : pathVertex a x b m = x i := by
  rcases pathVertex_cases a x b m with ⟨hm, -⟩ | ⟨i', hm, h'⟩ | ⟨hm, -⟩
  · omega
  · rw [h', show i' = i from Fin.ext (by omega)]
  · omega

/-- **An interior position, by index** (Phase 40g CHAIN): the index `j + 1` is sent to the interior
body `x j` (`pathVertex_eq_of_val_eq_succ` at a literal index). -/
theorem pathVertex_val_succ {k : ℕ} (a : α) (x : Fin k → α) (b : α) (j : ℕ) (hj : j < k) :
    pathVertex a x b ⟨j + 1, by omega⟩ = x ⟨j, hj⟩ :=
  pathVertex_eq_of_val_eq_succ a x b rfl

/-- **A path of distinct bodies has an injective sequence** (Phase 40g CHAIN): with the interior
bodies distinct and different from both ends, and `a ≠ b`, no two positions carry the same body.
Read off position by position (`pathVertex_cases`). -/
theorem pathVertex_injective {k : ℕ} {x : Fin k → α} {a b : α} (hinj : Function.Injective x)
    (hax : ∀ i, x i ≠ a) (hbx : ∀ i, x i ≠ b) (hab : a ≠ b) :
    Function.Injective (pathVertex a x b) := by
  intro m m' h
  rcases pathVertex_cases a x b m with ⟨hm, h1⟩ | ⟨i, hm, h1⟩ | ⟨hm, h1⟩ <;>
  rcases pathVertex_cases a x b m' with ⟨hm', h2⟩ | ⟨i', hm', h2⟩ | ⟨hm', h2⟩ <;>
  rw [h1, h2] at h
  · exact Fin.ext (by omega)
  · exact absurd h.symm (hax i')
  · exact absurd h hab
  · exact absurd h (hax i)
  · rw [hinj h] at hm; exact Fin.ext (by omega)
  · exact absurd h (hbx i)
  · exact absurd h.symm hab
  · exact absurd h.symm (hbx i')
  · exact Fin.ext (by omega)

/-- **Where an interior body sits in the path sequence** (Phase 40g CHAIN): with the interior
bodies distinct and different from both ends, `x i` sits exactly at the index of value `i + 1`. No
injectivity of the whole sequence is needed, so `a = b` (a closed ear) is allowed. -/
theorem pathVertex_eq_x_iff {k : ℕ} {x : Fin k → α} {a b : α} (hinj : Function.Injective x)
    (hax : ∀ i, x i ≠ a) (hbx : ∀ i, x i ≠ b) (m : Fin (k + 2)) (i : Fin k) :
    pathVertex a x b m = x i ↔ m.val = i.val + 1 := by
  rcases pathVertex_cases a x b m with ⟨hm, h⟩ | ⟨i', hm, h⟩ | ⟨hm, h⟩
  · rw [h]; exact ⟨fun h' => absurd h'.symm (hax i), fun h' => by omega⟩
  · rw [h]; exact ⟨fun h' => by rw [hinj h'] at hm; exact hm,
      fun h' => congrArg x (Fin.ext (by omega))⟩
  · rw [h]; exact ⟨fun h' => absurd h'.symm (hbx i), fun h' => by omega⟩

/-- **The path read from its other end** (Phase 40e BRIDGE): `pathVertex b (x ∘ Fin.rev) a` is
`pathVertex a x b` backwards. This is the path as seen from `b`'s side, where the fibre lemma
`Graph.exists_liftingRestrict_eq_of_bridgePath` is applied a second time. -/
theorem pathVertex_rev {k : ℕ} (a : α) (x : Fin k → α) (b : α) (m : Fin (k + 2)) :
    pathVertex b (x ∘ Fin.rev) a m = pathVertex a x b m.rev := by
  have hrev := Fin.val_rev m
  rcases pathVertex_cases b (x ∘ Fin.rev) a m with ⟨hm, h⟩ | ⟨i, hm, h⟩ | ⟨hm, h⟩
  · rw [h]
    rcases pathVertex_cases a x b m.rev with ⟨hm', -⟩ | ⟨i', hm', -⟩ | ⟨-, h'⟩
    · omega
    · omega
    · exact h'.symm
  · rw [h]
    rcases pathVertex_cases a x b m.rev with ⟨hm', -⟩ | ⟨i', hm', h'⟩ | ⟨hm', -⟩
    · omega
    · rw [h', Function.comp_apply]
      congr 1
      ext
      simp [Fin.val_rev]
      omega
    · omega
  · rw [h]
    rcases pathVertex_cases a x b m.rev with ⟨-, h'⟩ | ⟨i', hm', -⟩ | ⟨hm', -⟩
    · exact h'.symm
    · omega
    · omega

/-- **Dropping the first interior body shifts the path sequence** (Phase 40g CHAIN): the sequence
from `x 0` through `x 1, …, x (k − 1)` to `d` is `pathVertex c x d` read from index `1` on. The
closed ear reads its far side as a cycle through `x 0` with it. -/
theorem pathVertex_shift {k : ℕ} (hk : 1 ≤ k) (c d : α) (x : Fin k → α) (m : Fin ((k - 1) + 2)) :
    pathVertex (x ⟨0, (by omega)⟩) (fun j : Fin (k - 1) => x ⟨j.val + 1, (by omega)⟩) d m
      = pathVertex c x d ⟨m.val + 1, (by omega)⟩ := by
  rcases pathVertex_cases (x ⟨0, (by omega)⟩) (fun j : Fin (k - 1) => x ⟨j.val + 1, (by omega)⟩) d m
    with ⟨hm, h⟩ | ⟨i, hm, h⟩ | ⟨hm, h⟩
  · rw [h, pathVertex_eq_of_val_eq_succ c x d (i := ⟨0, (by omega)⟩) (by simp [hm])]
  · rw [h, pathVertex_eq_of_val_eq_succ c x d (i := ⟨i.val + 1, (by omega)⟩) (by simp [hm])]
  · rw [h]
    have : (⟨m.val + 1, (by omega)⟩ : Fin (k + 2)) = Fin.last (k + 1) := Fin.ext (by simp; omega)
    rw [this, pathVertex_last]

/-- **Which path positions lie in a prefix** (Phase 40e BRIDGE): for `j ≤ k`, the prefix
`V₁ ∪ {x i | i < j}` contains exactly the path positions `0, …, j`, that is `a` and the first `j`
interior bodies. This needs the interior bodies distinct and outside `V₁`, and `b` outside `V₁`
and not an interior body. -/
theorem pathVertex_mem_union_image_iff {k : ℕ} {V₁ : Set α} {x : Fin k → α} {a b : α}
    (hxV₁ : ∀ i, x i ∉ V₁) (hinj : Function.Injective x) (ha : a ∈ V₁) (hb : b ∉ V₁)
    (hbx : ∀ i, x i ≠ b) {j : ℕ} (hj : j ≤ k) (m : Fin (k + 2)) :
    pathVertex a x b m ∈ V₁ ∪ x '' {i | i.val < j} ↔ m.val ≤ j := by
  rcases pathVertex_cases a x b m with ⟨hm, h⟩ | ⟨i, hm, h⟩ | ⟨hm, h⟩
  · rw [h, hm]
    exact ⟨fun _ => Nat.zero_le _, fun _ => Or.inl ha⟩
  · rw [h, hm]
    constructor
    · rintro (h1 | ⟨i', hi', hii'⟩)
      · exact absurd h1 (hxV₁ i)
      · rw [hinj hii'] at hi'
        exact hi'
    · intro hij
      exact Or.inr ⟨i, by simp only [Set.mem_ofPred_eq]; omega, rfl⟩
  · rw [h, hm]
    constructor
    · rintro (h1 | ⟨i', -, hi'⟩)
      · exact absurd h1 hb
      · exact absurd hi' (hbx i')
    · intro hkj
      omega

/-- **The only edge leaving a prefix of the path is the next path edge** (Phase 40e BRIDGE): for
`j ≤ k`, the one edge of `G` with exactly one end in `V₁ ∪ {x i | i < j}` is `e j`, from position
`j` to position `j + 1`. Every other edge lies inside `V₁` or inside `V₂` (`hsep`), and a path edge
`e i` with `i ≠ j` has both ends on one side of the prefix (`pathVertex_mem_union_image_iff`). At
`j = k` this is the last bridge, into `V₂`. -/
theorem _root_.Graph.cutEdges_union_image_of_bridgePath {G : Graph α β} {V₁ V₂ : Set α}
    (hdisj : Disjoint V₁ V₂) {k : ℕ} {x : Fin k → α} (hxV₁ : ∀ i, x i ∉ V₁)
    (hxV₂ : ∀ i, x i ∉ V₂) (hinj : Function.Injective x) {a b : α} (ha : a ∈ V₁) (hb : b ∈ V₂)
    {e : Fin (k + 1) → β}
    (hpath : ∀ i : Fin (k + 1),
      G.IsLink (e i) (pathVertex a x b i.castSucc) (pathVertex a x b i.succ))
    (hsep : ∀ f u v, G.IsLink f u v → (∀ i, f ≠ e i) →
      (u ∈ V₁ ∧ v ∈ V₁) ∨ (u ∈ V₂ ∧ v ∈ V₂))
    {j : ℕ} (hj : j ≤ k) :
    G.cutEdges (V₁ ∪ x '' {i | i.val < j}) = {e ⟨j, Nat.lt_succ_of_le hj⟩} := by
  have hmem := pathVertex_mem_union_image_iff hxV₁ hinj ha
    (fun h => Set.disjoint_left.mp hdisj h hb) (fun i h => hxV₂ i (h ▸ hb)) hj
  ext f
  simp only [Graph.cutEdges, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨-, u, v, hl, hu, hv⟩
    by_cases hf : ∃ i, f = e i
    · obtain ⟨i, rfl⟩ := hf
      rcases hl.eq_and_eq_or_eq_and_eq (hpath i) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [hmem] at hu hv
        simp only [Fin.val_castSucc, Fin.val_succ] at hu hv
        exact congrArg e (Fin.ext (by simp only; omega))
      · rw [hmem] at hu hv
        simp only [Fin.val_castSucc, Fin.val_succ] at hu hv
        omega
    · rcases hsep f u v hl (fun i h => hf ⟨i, h⟩) with ⟨-, hv1⟩ | ⟨hu2, -⟩
      · exact absurd (Or.inl hv1) hv
      · rcases hu with hu1 | ⟨i, -, rfl⟩
        · exact absurd hu2 (Set.disjoint_left.mp hdisj hu1)
        · exact absurd hu2 (hxV₂ i)
  · rintro rfl
    refine ⟨(hpath _).edge_mem, _, _, hpath _, ?_, ?_⟩
    · rw [hmem]; simp
    · rw [hmem]; simp

/-- **The full prefix is every interior body**: `{x i | i < k} = range x` for `x : Fin k → α`. -/
theorem image_val_lt_eq_range {k : ℕ} (x : Fin k → α) :
    x '' {i | i.val < k} = Set.range x := by
  ext w; simp [Fin.is_lt]

private theorem union_image_val_lt_succ {k : ℕ} (V₁ : Set α) (x : Fin k → α) {j : ℕ}
    (hj : j < k) :
    V₁ ∪ x '' {i | i.val < j + 1} = (V₁ ∪ x '' {i | i.val < j}) ∪ {x ⟨j, hj⟩} := by
  ext w
  simp only [Set.mem_union, Set.mem_image, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro (h | ⟨i, hi, rfl⟩)
    · exact Or.inl (Or.inl h)
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | hi
      · exact Or.inl (Or.inr ⟨i, hi, rfl⟩)
      · exact Or.inr (congrArg x (Fin.ext hi))
  · rintro ((h | ⟨i, hi, rfl⟩) | rfl)
    · exact Or.inl h
    · exact Or.inr ⟨i, by omega, rfl⟩
    · exact Or.inr ⟨_, by simp, rfl⟩

/-- **Each path body adds one to the deficiency** (`lem:cut-edge-decomposition` along the path;
Phase 40e BRIDGE): `def(G[V₁ ∪ {x 0, …, x (k − 1)}]) = def(G[V₁]) + k`. Adding the bodies one at a
time, `x j` hangs from the prefix before it by the single edge `e j`
(`Graph.cutEdges_union_image_of_bridgePath`), so KT Lemma 3.6 in its pendant form
`Graph.deficiency_induce_union_singleton` adds `1` at each step. -/
theorem _root_.Graph.deficiency_induce_union_range_of_bridgePath [Finite α] [Finite β]
    {G : Graph α β} [G.Loopless] {n : ℕ} (hD : 1 ≤ Graph.bodyBarDim n) {V₁ V₂ : Set α}
    (hdisj : Disjoint V₁ V₂) {k : ℕ} {x : Fin k → α} (hxV₁ : ∀ i, x i ∉ V₁)
    (hxV₂ : ∀ i, x i ∉ V₂) (hinj : Function.Injective x) {a b : α} (ha : a ∈ V₁) (hb : b ∈ V₂)
    {e : Fin (k + 1) → β}
    (hpath : ∀ i : Fin (k + 1),
      G.IsLink (e i) (pathVertex a x b i.castSucc) (pathVertex a x b i.succ))
    (hsep : ∀ f u v, G.IsLink f u v → (∀ i, f ≠ e i) →
      (u ∈ V₁ ∧ v ∈ V₁) ∨ (u ∈ V₂ ∧ v ∈ V₂)) :
    (G.induce (V₁ ∪ Set.range x)).deficiency n = (G.induce V₁).deficiency n + k := by
  have hmem := fun j (hj : j ≤ k) => pathVertex_mem_union_image_iff hxV₁ hinj ha
    (fun h => Set.disjoint_left.mp hdisj h hb) (fun i h => hxV₂ i (h ▸ hb)) hj
  have hstep : ∀ j, j ≤ k → (G.induce (V₁ ∪ x '' {i | i.val < j})).deficiency n
      = (G.induce V₁).deficiency n + j := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      have hjk : j < k := hj
      have hxj : pathVertex a x b (⟨j, by omega⟩ : Fin (k + 1)).succ = x ⟨j, hjk⟩ :=
        pathVertex_eq_of_val_eq_succ a x b (by simp)
      have hl := hpath ⟨j, by omega⟩
      rw [hxj] at hl
      rw [union_image_val_lt_succ V₁ x hjk,
        Graph.deficiency_induce_union_singleton hD hl
          ((hmem _ hjk.le _).mpr (by simp))
          (by rw [← hxj, hmem _ hjk.le]; simp)
          (by rw [Graph.cutEdges_union_image_of_bridgePath hdisj hxV₁ hxV₂ hinj ha hb hpath hsep
            hjk.le, Set.ncard_singleton]),
        ih hjk.le]
      push_cast
      ring
  simpa [image_val_lt_eq_range] using hstep k le_rfl

/-- **Each path body adds at least `D − 1` to the rank** (`lem:block-rank-cut` along the path;
Phase 40e BRIDGE): with every hinge nonzero,
`finrank(G[V₁]) + (screwDim d − 1)·k ≤ finrank(G[V₁ ∪ {x 0, …, x (k − 1)}])`. As for the
deficiency (`Graph.deficiency_induce_union_range_of_bridgePath`), with the pendant-body brick
`BodyHingeFramework.add_le_finrank_span_rigidityRows_induce_union_singleton` at each step. -/
theorem BodyHingeFramework.add_le_finrank_span_rigidityRows_induce_union_range_of_bridgePath
    {d : ℕ} [Finite α] [Finite β] {G : Graph α β} (ext : β → ScrewSpace K d)
    (hext : ∀ e u v, G.IsLink e u v → ext e ≠ 0) {V₁ V₂ : Set α}
    (hdisj : Disjoint V₁ V₂) {k : ℕ} {x : Fin k → α} (hxV₁ : ∀ i, x i ∉ V₁)
    (hxV₂ : ∀ i, x i ∉ V₂) (hinj : Function.Injective x) {a b : α} (ha : a ∈ V₁) (hb : b ∈ V₂)
    {e : Fin (k + 1) → β}
    (hpath : ∀ i : Fin (k + 1),
      G.IsLink (e i) (pathVertex a x b i.castSucc) (pathVertex a x b i.succ))
    (hsep : ∀ f u v, G.IsLink f u v → (∀ i, f ≠ e i) →
      (u ∈ V₁ ∧ v ∈ V₁) ∨ (u ∈ V₂ ∧ v ∈ V₂)) :
    Module.finrank K (Submodule.span K
        (⟨G.induce V₁, ext⟩ : BodyHingeFramework K d α β).rigidityRows) + (screwDim d - 1) * k
      ≤ Module.finrank K (Submodule.span K
        (⟨G.induce (V₁ ∪ Set.range x), ext⟩ : BodyHingeFramework K d α β).rigidityRows) := by
  have hmem := fun j (hj : j ≤ k) => pathVertex_mem_union_image_iff hxV₁ hinj ha
    (fun h => Set.disjoint_left.mp hdisj h hb) (fun i h => hxV₂ i (h ▸ hb)) hj
  have hstep : ∀ j, j ≤ k → Module.finrank K (Submodule.span K
        (⟨G.induce V₁, ext⟩ : BodyHingeFramework K d α β).rigidityRows) + (screwDim d - 1) * j
      ≤ Module.finrank K (Submodule.span K (⟨G.induce (V₁ ∪ x '' {i | i.val < j}), ext⟩ :
        BodyHingeFramework K d α β).rigidityRows) := by
    intro j
    induction j with
    | zero =>
      intro _
      rw [show x '' {i : Fin k | i.val < 0} = ∅ by simp, Set.union_empty, Nat.mul_zero,
        Nat.add_zero]
    | succ j ih =>
      intro hj
      have hjk : j < k := hj
      have hxj : pathVertex a x b (⟨j, by omega⟩ : Fin (k + 1)).succ = x ⟨j, hjk⟩ :=
        pathVertex_eq_of_val_eq_succ a x b (by simp)
      have hl := hpath ⟨j, by omega⟩
      rw [hxj] at hl
      have hu₀ := (hmem _ hjk.le (Fin.castSucc ⟨j, by omega⟩)).mpr (by simp)
      have hw₀ : x ⟨j, hjk⟩ ∉ V₁ ∪ x '' {i | i.val < j} := by
        rw [← hxj, hmem _ hjk.le]
        simp
      have hcut := Graph.cutEdges_union_image_of_bridgePath hdisj hxV₁ hxV₂ hinj ha hb hpath hsep
        hjk.le
      have h1 := BodyHingeFramework.add_le_finrank_span_rigidityRows_induce_union_singleton ext hl
        hu₀ hw₀ (fun f u hf hu => Graph.eq_cutEdge_of_isLink_crossing hl hu₀ hw₀
          (by rw [hcut, Set.ncard_singleton]) hf hu hw₀) hext
      rw [union_image_val_lt_succ V₁ x hjk]
      have := ih hjk.le
      rw [Nat.mul_succ]
      omega
  have := hstep k le_rfl
  rwa [image_val_lt_eq_range] at this

/-- **BRIDGE** (`thm:pencil-x0-bridge`; (MC-53)(iv), the half the induction uses): if `G` satisfies
(H), `V(G)` is the disjoint union of `V₁`, `V₂` and the distinct interior bodies
`x 0, …, x (k − 1)` of a path `a − x 0 − ⋯ − x (k − 1) − b` from `a ∈ V₁` to `b ∈ V₂` (`hpath`,
along `pathVertex`; `k ≥ 0`), every other edge lies inside `V₁` or inside `V₂`, and `X₀` attains at
`G[V₁]` and at `G[V₂]`, then `X₀(G)` attains.

As for CUT: one picture generic for both sides and main for `G`, and heights on which both
restrictions attain (`Graph.exists_liftingRestrict_eq_of_bridgePath`, applied from `V₂` along the
reversed path, `pathVertex_rev`). The counts: the last bridge is the only edge leaving
`V₁ ∪ range x`, whose complement is `V₂`, so the cut-edge brick
`BodyHingeFramework.le_finrank_span_rigidityRows_of_cut` and KT Lemma 3.6
`Graph.deficiency_eq_of_cutEdges_ncard_le_one` add `5` to the rank and `1` to the deficiency; along
the path each body adds at least `5` and exactly `1` again
(`BodyHingeFramework.add_le_finrank_span_rigidityRows_induce_union_range_of_bridgePath`,
`Graph.deficiency_induce_union_range_of_bridgePath`), and `6` to the body term. So the rank is at
least the two sides' targets plus `5(k + 1)`, which is the target of `G`. -/
theorem _root_.Graph.X0Attains.of_bridgePath [Infinite K] [Finite α] [Finite β] {G : Graph α β}
    (hG : G.IsX0Graph) {V₁ V₂ : Set α} {k : ℕ} {x : Fin k → α} {a b : α} {e : Fin (k + 1) → β}
    (hcover : V(G) = V₁ ∪ Set.range x ∪ V₂) (hdisj : Disjoint V₁ V₂)
    (hxV₁ : ∀ i, x i ∉ V₁) (hxV₂ : ∀ i, x i ∉ V₂) (hinj : Function.Injective x)
    (ha : a ∈ V₁) (hb : b ∈ V₂)
    (hpath : ∀ i : Fin (k + 1),
      G.IsLink (e i) (pathVertex a x b i.castSucc) (pathVertex a x b i.succ))
    (hsep : ∀ f u v, G.IsLink f u v → (∀ i, f ≠ e i) →
      (u ∈ V₁ ∧ v ∈ V₁) ∨ (u ∈ V₂ ∧ v ∈ V₂))
    (h₁ : (G.induce V₁).X0Attains K) (h₂ : (G.induce V₂).X0Attains K) :
    G.X0Attains K := by
  classical
  have : Fintype α := Fintype.ofFinite α
  have hV : V(G).Nonempty := hG.connected.nonempty
  have : Inhabited α := ⟨hV.some⟩
  have : G.Loopless := hG.simple.toLoopless
  set S := V₁ ∪ Set.range x with hSdef
  have hSV : S ⊆ V(G) := hcover ▸ Set.subset_union_left
  have hV₁ : V₁ ⊆ V(G) := Set.subset_union_left.trans hSV
  have hV₂ : V₂ ⊆ V(G) := hcover ▸ Set.subset_union_right
  have hle₁ : G.induce V₁ ≤ G := Graph.induce_le hV₁
  have hle₂ : G.induce V₂ ≤ G := Graph.induce_le hV₂
  have hbV₁ : b ∉ V₁ := fun h => Set.disjoint_left.mp hdisj h hb
  have haV₂ : a ∉ V₂ := fun h => Set.disjoint_left.mp hdisj ha h
  have hSV₂ : Disjoint S V₂ := by
    refine Set.disjoint_union_left.mpr ⟨hdisj, Set.disjoint_left.mpr ?_⟩
    rintro _ ⟨i, rfl⟩
    exact hxV₂ i
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
  -- the heights restrict onto each side: from `V₁` along the path, from `V₂` along its reverse
  have hex₁ : ∃ z ∈ G.liftingSpace q, MvPolynomial.eval z (restrictPoly V₁ R₁) ≠ 0 := by
    have hsep₁ : ∀ f u v, G.IsLink f u v → (∀ i, f ≠ e i) →
        (u ∈ V₁ ∧ v ∈ V₁) ∨ (u ∉ V₁ ∧ v ∉ V₁) := by
      intro f u v hf hfe
      rcases hsep f u v hf hfe with h | ⟨hu, hv⟩
      · exact Or.inl h
      · exact Or.inr ⟨fun h => Set.disjoint_left.mp hdisj h hu,
          fun h => Set.disjoint_left.mp hdisj h hv⟩
    obtain ⟨z, hz, hzr⟩ :=
      Graph.exists_liftingRestrict_eq_of_bridgePath hV₁ hxV₁ ha hbV₁ hpath hsep₁ hz₁
    exact ⟨z, hz, by rwa [eval_restrictPoly, hzr]⟩
  have hex₂ : ∃ z ∈ G.liftingSpace q, MvPolynomial.eval z (restrictPoly V₂ R₂) ≠ 0 := by
    have hpath₂ : ∀ i : Fin (k + 1), G.IsLink ((e ∘ Fin.rev) i)
        (pathVertex b (x ∘ Fin.rev) a i.castSucc) (pathVertex b (x ∘ Fin.rev) a i.succ) := by
      intro i
      rw [pathVertex_rev, pathVertex_rev, Fin.rev_castSucc, Fin.rev_succ, Function.comp_apply]
      exact (hpath i.rev).symm
    have hsep₂ : ∀ f u v, G.IsLink f u v → (∀ i, f ≠ (e ∘ Fin.rev) i) →
        (u ∈ V₂ ∧ v ∈ V₂) ∨ (u ∉ V₂ ∧ v ∉ V₂) := by
      intro f u v hf hfe
      rcases hsep f u v hf (fun i h => hfe i.rev (by simp [h])) with ⟨hu, hv⟩ | h
      · exact Or.inr ⟨fun h => Set.disjoint_left.mp hdisj hu h,
          fun h => Set.disjoint_left.mp hdisj hv h⟩
      · exact Or.inl h
    obtain ⟨z, hz, hzr⟩ := Graph.exists_liftingRestrict_eq_of_bridgePath hV₂
      (fun i => hxV₂ _) hb haV₂ hpath₂ hsep₂ hz₂
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
  -- the last bridge is the only edge leaving `S = V₁ ∪ range x`, whose complement is `V₂`
  have hcut : G.cutEdges S = {e (Fin.last k)} := by
    have := Graph.cutEdges_union_image_of_bridgePath hdisj hxV₁ hxV₂ hinj ha hb hpath hsep le_rfl
    rwa [image_val_lt_eq_range] at this
  have hVS : V(G) \ S = V₂ := by
    rw [hcover, Set.union_sdiff_left]
    exact hSV₂.symm.sdiff_eq_left
  set F := (PanelHingeFramework.ofNormals (k := 2) G ends
    (fun p => pencilConfigPoint q z p.1 p.2)).toBodyHinge with hFdef
  have hext : ∀ f u w, G.IsLink f u w → F.supportExtensor f ≠ 0 :=
    fun f u w hf => hqmain.1.supportExtensor_ne_zero hends z hf
  -- the ranks: at least `5` for the last bridge, and for each path body
  have hbrick := BodyHingeFramework.le_finrank_span_rigidityRows_of_cut F (V₁ := S)
    (C := {e (Fin.last k)}) (by simp) hext
    (fun f u w hf hfC => by
      by_cases hu : u ∈ S <;> by_cases hw : w ∈ S
      · exact Or.inl ⟨hu, hw⟩
      · have hfS : f ∈ G.cutEdges S := ⟨hf.edge_mem, u, w, hf, hu, hw⟩
        exact absurd (hcut ▸ hfS) hfC
      · have hfS : f ∈ G.cutEdges S := ⟨hf.edge_mem, w, u, hf.symm, hw, hu⟩
        exact absurd (hcut ▸ hfS) hfC
      · exact Or.inr ⟨hu, hw⟩)
    (fun f hf => by rw [← hcut] at hf; exact hf.2)
  have hpathrank :=
    BodyHingeFramework.add_le_finrank_span_rigidityRows_induce_union_range_of_bridgePath
      F.supportExtensor hext hdisj hxV₁ hxV₂ hinj ha hb hpath hsep
  -- the deficiencies: `1` for the last bridge, and for each path body
  have hdefS := Graph.deficiency_induce_union_range_of_bridgePath (n := 3) (by decide) hdisj
    hxV₁ hxV₂ hinj ha hb hpath hsep
  have hSne : S.Nonempty := ⟨a, Or.inl ha⟩
  have hSssub : S ⊂ V(G) := (Set.ssubset_iff_of_subset hSV).mpr
    ⟨b, hV₂ hb, fun h => Set.disjoint_left.mp hSV₂ h hb⟩
  have hdef := Graph.deficiency_eq_of_cutEdges_ncard_le_one (n := 3) (by decide) hSne hSssub
    (by rw [hcut, Set.ncard_singleton])
  rw [hcut, Set.ncard_singleton, hVS] at hdef
  -- the body counts
  have hcountS : S.ncard = V₁.ncard + k := by
    rw [hSdef, Set.ncard_union_eq _ (Set.toFinite _) (Set.toFinite _),
      Set.ncard_range_of_injective hinj, Nat.card_eq_fintype_card, Fintype.card_fin]
    refine Set.disjoint_left.mpr ?_
    rintro _ h ⟨i, rfl⟩
    exact hxV₁ i h
  have hcount : V(G).ncard = S.ncard + V₂.ncard := by
    rw [hcover, Set.ncard_union_eq hSV₂ (Set.toFinite _) (Set.toFinite _)]
  refine Graph.x0Attains_of_exists hV ends hends hqmain hz ?_
  have e1 : (Module.finrank K (Submodule.span K (PanelHingeFramework.ofNormals (k := 2)
        (G.induce S) ends (fun p => pencilConfigPoint q z p.1 p.2)).toBodyHinge.rigidityRows)
          : ℤ)
      + (screwDim 2 - 1) * 1
      + (Module.finrank K (Submodule.span K (PanelHingeFramework.ofNormals (k := 2)
          (G.induce V₂) ends (fun p => pencilConfigPoint q z p.1 p.2)).toBodyHinge.rigidityRows)
            : ℤ)
      ≤ (Module.finrank K (Submodule.span K F.rigidityRows) : ℤ) := by
    have := hbrick
    simp only [Set.ncard_singleton] at this
    rw [show V(F.graph) \ S = V₂ from hVS] at this
    exact_mod_cast this
  have e2 : (Module.finrank K (Submodule.span K (PanelHingeFramework.ofNormals (k := 2)
        (G.induce V₁) ends (fun p => pencilConfigPoint q z p.1 p.2)).toBodyHinge.rigidityRows)
          : ℤ) + (screwDim 2 - 1) * k
      ≤ (Module.finrank K (Submodule.span K (PanelHingeFramework.ofNormals (k := 2)
        (G.induce S) ends (fun p => pencilConfigPoint q z p.1 p.2)).toBodyHinge.rigidityRows)
          : ℤ) := by
    exact_mod_cast hpathrank
  rw [hr₁, show screwDim 2 = 6 from rfl] at e2
  rw [hr₂, show screwDim 2 = 6 from rfl] at e1
  rw [show screwDim 2 = 6 from rfl, hdef, hdefS]
  have hb3 : (Graph.bodyBarDim 3 : ℤ) = 6 := rfl
  rw [hb3]
  push_cast at e1 e2 ⊢
  have hcount' : (V(G).ncard : ℤ) = V₁.ncard + k + V₂.ncard := by
    rw [hcount, hcountS]; push_cast; ring
  rw [hcount']
  linarith

end CombinatorialRigidity.Molecular
