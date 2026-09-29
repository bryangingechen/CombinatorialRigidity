/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.Molecule.Pencil.MainComponent.EarGen

/-!
# Open ears with two, three or four interior bodies (Phase 40h SHORT)

The ear steps of the `X₀` induction for an open ear `a − x 0 − ⋯ − x (k − 1) − b` on `V₁` with a
few interior bodies, whose ends may be adjacent (`blueprint/src/chapter/main-component.tex`,
`sec:main-component-short`; informal (MC-180), (MC-181) of Step MC13 and (MC-54) of Step MC14,
§(K-main)). Every step shares CUT's contract (`MainComponent/Cut.lean`): it concludes
`Graph.X0Attains K` at `G` from attainment at smaller graphs on the same `α`, `β`, and ends at
`Graph.x0Attains_of_exists`. By the ear rank law
(`BodyHingeFramework.finrank_span_rigidityRows_ear_eq`) the step reduces to a lower bound on
`dim(ρ + Λ)`, the relative screws of `G[V₁]` plus the ear's joins. With two interior bodies three
independent joins suffice, given that the deficiency does not drop. With three or four interior
bodies the step also uses the antecedent `G″ = G.splitOff (x 1) (x 0) (x 2) (e 1)`, `G` with its
second interior body suppressed and the freed label relinked, and puts `x 1` back
(`exists_insertion_three`, `exists_insertion_four`, `MainComponent/Lines.lean`).

## Main statements

* `Graph.X0Attains.of_openEar_two` — **(MC-54) at `k = 2`**, the open ear with two interior
  bodies, under `def₃(G[V₁]) ≤ def₃(G)`.
* `splitOff_ear_four`, `splitOff_ear_three`, `induce_splitOff_ear` — suppressing `x 1` leaves
  the ear `a − x 0 − x 2 − x 3 − b`, resp. `a − x 0 − x 2 − b`, on `V₁`, with the same subgraph on
  `V₁`;
  `Graph.isLink_update_splitOff` — a selector of `G`, relinked at the freed label, orients the
  split-off.
* `linearIndependent_tetra_witness` — the four points of the tetrahedron witness are independent.
* `Graph.exists_earBase_splitOff` — the base data of the steps with an antecedent (informal
  (MC-180), (MC-181) Steps 1–2): a picture and heights at which `G[V₁]` and the antecedent attain,
  fixed before the ear data, and what every ear datum then reads on `V₁`.
* `Graph.X0Attains.of_openEar_four` — **(MC-180)**, the open ear with four interior bodies.
* `Graph.X0Attains.of_openEar_three` — **(MC-181)**, the open ear with three interior bodies.

## Design

* **Two interior bodies need no antecedent and no ear data.** The heights `0` lie in every
  `L_G(q)`, and a flat certificate (three joins of the closed hexagon) makes the three ear joins
  independent there, as `Graph.X0Attains.of_openEar` does with six.
* **The base data are fixed first, the ear data second** (`MainComponent/EarGen.lean`). One
  parametrization, `G`'s ear data, serves `G` and `G″`: the coordinates of `x 1` are invisible to
  `G″`, so `G″`'s rank is read at `ofNormals G″` of the same configuration.
* **Two rounds of common non-roots, no determinant.** Round 1 picks ear data at which `G″` has its
  target rank, its picture is admissible, and the six joins of `x 0, x 2, x 3, b` span `Λ²K⁴`,
  certified at an explicit witness (`linearIndependent_tetra_witness`) by the span transfer
  `exists_mvPolynomial_le_finrank_sup_span_pointJoin`. Round 2 picks ear data of `G` off the span
  bound for `dim(ρ + Λ)` at the reinserted point and off `G`'s main-picture polynomial.
* **The span transfer needs no nonzero hinge at its witness; the rank transfer does.** So the
  reinserted point certifies `dim(ρ + Λ)`, not `G`'s rank, and in the branch `W = Λ²K⁴` it may
  collide with `x 0` (`exists_insertion_four`, `exists_insertion_three`).
* **At three interior bodies the case split on `ρ` comes before the ear data.** If some `c ∈ ρ`
  pairs to a nonzero value with a line joining the planes at `a` and `b`, round 1 also asks
  `⟨c, y₁ ∧ y₃⟩ ≠ 0`, written as the span bound `dim(ker⟨c, ·⟩ + K (y₁ ∧ y₃)) ≥ 6` so that the
  span transfer applies, with its witness at an affine pair
  (`exists_klein_liftPlane_affine_ne_zero`).
-/

open scoped Graph

namespace CombinatorialRigidity.Molecular

variable {K : Type*} [Field K] {α β : Type*}

/-! ## The open ear with two interior bodies -/

/-- **(MC-54) at `k = 2`, the open ear with two interior bodies** (`thm:pencil-x0-open-ear-two`).
Let `G` satisfy (H), with an open ear `a − x 0 − x 1 − b` on `V₁` whose ends may be adjacent, and
let `def₃(G[V₁]) ≤ def₃(G)`, which replaces (MC-54)'s `δ = 0` (the PI's decision 4(a),
`notes/Phase40h.md`; `Graph.deficiency_induce_le_of_ear_of_merge` supplies it from a tight partition
of `G[V₁]` with `a`, `b` in one part). If `X₀(G[V₁])` attains, `X₀(G)` attains; there is no
antecedent. The heights `0` lie in every `L_G(q)`, and there the three ear joins are independent
at a certificate picture putting `a, x 0, x 1, b` at `Y₄, Y₅, Y₀, Y₁`: three joins of the closed
hexagon (`linearIndependent_pointJoin_certHexagon`). Independence is open in the picture, then in
the heights, as in `Graph.X0Attains.of_openEar`. So the ear rank law adds at least `5 · 3 + 3 − 6`
to the rank, the growth of the target when the deficiency does not drop. -/
theorem _root_.Graph.X0Attains.of_openEar_two [Infinite K] [Finite α] [Finite β]
    {G : Graph α β} (hG : G.IsX0Graph) {V₁ : Set α} {x : Fin 2 → α} {a b : α}
    {e : Fin 3 → β} (hcover : V(G) = V₁ ∪ Set.range x) (hinj : Function.Injective x)
    (hxV₁ : ∀ i, x i ∉ V₁) (ha : a ∈ V₁) (hb : b ∈ V₁) (hab : a ≠ b)
    (hpath : ∀ i : Fin 3,
      G.IsLink (e i) (pathVertex a x b i.castSucc) (pathVertex a x b i.succ))
    (hsep : ∀ f u w, G.IsLink f u w → (∀ i, f ≠ e i) → u ∈ V₁ ∧ w ∈ V₁)
    (h₁ : (G.induce V₁).X0Attains K)
    (hdef : (G.induce V₁).deficiency 3 ≤ G.deficiency 3) : G.X0Attains K := by
  classical
  have : Fintype α := Fintype.ofFinite α
  have hV : V(G).Nonempty := hG.connected.nonempty
  have : Inhabited α := ⟨a⟩
  have hV₁G : V₁ ⊆ V(G) := hcover ▸ Set.subset_union_left
  have hle₁ : G.induce V₁ ≤ G := Graph.induce_le hV₁G
  have hax : ∀ i, x i ≠ a := fun i h => hxV₁ i (h ▸ ha)
  have hbx : ∀ i, x i ≠ b := fun i h => hxV₁ i (h ▸ hb)
  have x01 : x 0 ≠ x 1 := fun h => absurd (hinj h) (by decide)
  obtain ⟨ends₁, P₁, hends₁, hP₁, hgood₁⟩ := h₁
  obtain ⟨Pm, hPm, hmain⟩ := G.exists_mvPolynomial_isMainPicture (K := K)
    hG.simple.toLoopless hG.three_le_ncard_closedNbhd
  set ends := G.endsOf
  have hends : ∀ f u w, G.IsLink f u w → G.IsLink f (ends f).1 (ends f).2 :=
    fun f _ _ hf => G.isLink_endsOf hf.edge_mem
  have hendsI : ∀ f u w, (G.induce V₁).IsLink f u w →
      (G.induce V₁).IsLink f (ends f).1 (ends f).2 := by
    intro f u w hf
    have hl := hends f u w hf.1
    rcases hl.eq_and_eq_or_eq_and_eq hf.1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨hl, h1 ▸ hf.2.1, h2 ▸ hf.2.2⟩
    · exact ⟨hl, h1 ▸ hf.2.2, h2 ▸ hf.2.1⟩
  -- the three ear links `a x 0, x 0 x 1, x 1 b`
  set u3 : Fin 3 → α := ![a, x 0, x 1]
  set v3 : Fin 3 → α := ![x 0, x 1, b]
  set f3 : Fin 3 → β := ![e 0, e 1, e 2]
  have hl3 : ∀ i, G.IsLink (f3 i) (u3 i) (v3 i) := by
    intro i
    fin_cases i
    · exact hpath 0
    · exact hpath 1
    · exact hpath 2
  -- the flat certificate: `a, x 0, x 1, b` at `Y₄, Y₅, Y₀, Y₁`, at the heights `0`
  set lab : α → Fin 6 := fun w => if w = x 0 then 5 else if w = x 1 then 0 else if w = b then 1
    else 4 with hlabdef
  set q₀ : α × Fin 2 → K := certPicture lab with hq₀def
  have hpt : ∀ w, pencilConfigPoint q₀ 0 w = certPt (lab w) := fun w => by
    rw [hq₀def]
    exact pencilConfigPoint_certPicture lab 0 w (by simp only [hlabdef]; split_ifs <;> rfl)
  have la : lab a = 4 := by simp [hlabdef, (hax _).symm, hab]
  have l0 : lab (x 0) = 5 := by simp [hlabdef]
  have l1 : lab (x 1) = 0 := by simp [hlabdef, x01.symm]
  have lb : lab b = 1 := by simp [hlabdef, (hbx _).symm]
  have hcert : LinearIndependent K
      (fun i => pointJoin (pencilConfigPoint q₀ 0 (u3 i)) (pencilConfigPoint q₀ 0 (v3 i))) := by
    have heq : (fun i =>
        pointJoin (pencilConfigPoint q₀ 0 (u3 i)) (pencilConfigPoint q₀ 0 (v3 i)))
        = (fun i : Fin 6 =>
          pointJoin (![certPt 0, certPt 1, certPt 2, certPt 3, certPt 4, certPt 5] i : Fin 4 → K)
            (![certPt 1, certPt 2, certPt 3, certPt 4, certPt 5, certPt 0] i)) ∘ ![4, 5, 0] := by
      funext i
      fin_cases i
      · change pointJoin (pencilConfigPoint q₀ 0 a) (pencilConfigPoint q₀ 0 (x 0)) = _
        rw [hpt, hpt, la, l0]; rfl
      · change pointJoin (pencilConfigPoint q₀ 0 (x 0)) (pencilConfigPoint q₀ 0 (x 1)) = _
        rw [hpt, hpt, l0, l1]; rfl
      · change pointJoin (pencilConfigPoint q₀ 0 (x 1)) (pencilConfigPoint q₀ 0 b) = _
        rw [hpt, hpt, l1, lb]; rfl
    rw [heq]
    exact linearIndependent_pointJoin_certHexagon.comp _ (by decide)
  -- the picture: generic for `G[V₁]`, main for `G`, the three joins independent at the heights `0`
  obtain ⟨Plam, hPlam₀, hPlam⟩ :=
    exists_mvPolynomial_linearIndependent_pointJoin_picture 0 u3 v3 hcert
  have hPlamne : Plam ≠ 0 := fun h => hPlam₀ (by rw [h, map_zero])
  obtain ⟨q, hq⟩ := MvPolynomial.exists_eval_ne_zero (mul_ne_zero (mul_ne_zero hP₁ hPm) hPlamne)
  rw [map_mul, map_mul] at hq
  obtain ⟨-, R₁, ⟨z₁, hz₁, hR₁⟩, hatt₁⟩ := hgood₁ q (left_ne_zero_of_mul (left_ne_zero_of_mul hq))
  have hqmain := hmain q (right_ne_zero_of_mul (left_ne_zero_of_mul hq))
  have hliq := hPlam q (right_ne_zero_of_mul hq)
  obtain ⟨Rlam, hRlam₀, hRlam⟩ :=
    exists_mvPolynomial_linearIndependent_pointJoin_heights q u3 v3 hliq
  -- heights on which `G[V₁]` attains and the three joins stay independent
  have hex₁ : ∃ z ∈ G.liftingSpace q, MvPolynomial.eval z (restrictPoly V₁ R₁) ≠ 0 := by
    obtain ⟨z, hz, hzr, -⟩ := G.earExtend_mem_liftingSpace (le_refl 2) hcover hinj hxV₁ ha hb hab
      hpath hsep hqmain.1 hz₁ 0
    exact ⟨z, hz, by rwa [eval_restrictPoly, hzr]⟩
  obtain ⟨z, hz, hz₁', hzlam⟩ :=
    MvPolynomial.exists_mem_eval_ne_zero₂ hex₁ ⟨0, Submodule.zero_mem _, hRlam₀⟩
  rw [eval_restrictPoly] at hz₁'
  have hr₁ := hatt₁ _ (Graph.liftingRestrict_mem_liftingSpace hle₁ hz) hz₁'
  have hli := hRlam z hzlam
  rw [Graph.vertexSet_induce G V₁] at hr₁
  rw [PanelHingeFramework.finrank_span_rigidityRows_ofNormals_congr _ hends₁ hendsI
    (q' := fun p => pencilConfigPoint q z p.1 p.2)
    (fun w hw t => pencilConfigPoint_liftingRestrict V₁ q z hw t)] at hr₁
  -- the ear rank law at `ofNormals G ends`, with three independent ear hinges
  set F := (PanelHingeFramework.ofNormals (k := 2) G ends
    (fun p => pencilConfigPoint q z p.1 p.2)).toBodyHinge
  have hC : ∀ i, F.supportExtensor (e i) ≠ 0 :=
    fun i => hqmain.1.supportExtensor_ne_zero hends z (hpath i)
  have hear := BodyHingeFramework.finrank_span_rigidityRows_ear_eq F hinj hxV₁ ha hb hab hpath
    hsep hC
  have hdim := card_le_finrank_of_linearIndependent_pointJoin hends (pencilConfigPoint q z) u3 v3
    f3 hl3 hli ((⟨F.graph.induce V₁, F.supportExtensor⟩ : BodyHingeFramework K 2 α β).relScrews a b
      ⊔ Submodule.span K (Set.range (F.supportExtensor ∘ e)))
    (fun i => Submodule.mem_sup_right (Submodule.subset_span (by fin_cases i <;> exact ⟨_, rfl⟩)))
  rw [Fintype.card_fin] at hdim
  -- the body count
  have hcount : (V(G).ncard : ℤ) = V₁.ncard + 2 := by
    rw [hcover, Set.ncard_union_eq _ (Set.toFinite _) (Set.toFinite _),
      Set.ncard_range_of_injective hinj, Nat.card_eq_fintype_card, Fintype.card_fin]
    · push_cast; ring
    · refine Set.disjoint_left.mpr ?_
      rintro _ h ⟨i, rfl⟩
      exact hxV₁ i h
  refine Graph.x0Attains_of_exists hV ends hends hqmain hz ?_
  have e1 : (Module.finrank K (Submodule.span K F.rigidityRows) : ℤ)
      = (Module.finrank K (Submodule.span K (PanelHingeFramework.ofNormals (k := 2) (G.induce V₁)
          ends (fun p => pencilConfigPoint q z p.1 p.2)).toBodyHinge.rigidityRows) : ℤ)
        + ((screwDim 2 : ℤ) - 1) * (2 + 1)
        + (Module.finrank K ↥((⟨F.graph.induce V₁, F.supportExtensor⟩ :
              BodyHingeFramework K 2 α β).relScrews a b
            ⊔ Submodule.span K (Set.range (F.supportExtensor ∘ e))) : ℤ)
        - (screwDim 2 : ℤ) := hear
  rw [e1, hr₁, hcount]
  have hs : (screwDim 2 : ℤ) = 6 := rfl
  rw [hs]
  have hdim' : (3 : ℤ) ≤ (Module.finrank K ↥((⟨F.graph.induce V₁, F.supportExtensor⟩ :
      BodyHingeFramework K 2 α β).relScrews a b
        ⊔ Submodule.span K (Set.range (F.supportExtensor ∘ e))) : ℤ) := by exact_mod_cast hdim
  linarith

/-! ## The antecedent `G″`: the ear with its second interior body suppressed -/

section Antecedent

/-- **The antecedent of the four-body ear is a three-body ear** (`thm:pencil-x0-open-ear-four`):
suppressing `x 1` and relinking `e 1` to `x 0 − x 2` leaves the ear
`a − x 0 − x 2 − x 3 − b` on `V₁`, with the labels `e 0, e 1, e 3, e 4`. -/
theorem splitOff_ear_four {G : Graph α β} {V₁ : Set α} {x : Fin 4 → α} {a b : α}
    {e : Fin 5 → β} (hcover : V(G) = V₁ ∪ Set.range x) (hinj : Function.Injective x)
    (hxV₁ : ∀ i, x i ∉ V₁) (ha : a ∈ V₁) (hb : b ∈ V₁) (hab : a ≠ b)
    (hpath : ∀ i : Fin 5,
      G.IsLink (e i) (pathVertex a x b i.castSucc) (pathVertex a x b i.succ))
    (hsep : ∀ f u w, G.IsLink f u w → (∀ i, f ≠ e i) → u ∈ V₁ ∧ w ∈ V₁) :
    V(G.splitOff (x 1) (x 0) (x 2) (e 1)) = V₁ ∪ Set.range ![x 0, x 2, x 3] ∧
      Function.Injective ![x 0, x 2, x 3] ∧ (∀ i, ![x 0, x 2, x 3] i ∉ V₁) ∧
      (∀ i : Fin 4, (G.splitOff (x 1) (x 0) (x 2) (e 1)).IsLink (![e 0, e 1, e 3, e 4] i)
        (pathVertex a ![x 0, x 2, x 3] b i.castSucc) (pathVertex a ![x 0, x 2, x 3] b i.succ)) ∧
      (∀ f u w, (G.splitOff (x 1) (x 0) (x 2) (e 1)).IsLink f u w →
        (∀ i, f ≠ ![e 0, e 1, e 3, e 4] i) → u ∈ V₁ ∧ w ∈ V₁) := by
  have hax : ∀ i, x i ≠ a := fun i h => hxV₁ i (h ▸ ha)
  have hbx : ∀ i, x i ≠ b := fun i h => hxV₁ i (h ▸ hb)
  have he := pathEdge_injective hinj hax hbx hab hpath
  have hx : ∀ i j, i ≠ j → x i ≠ x j := fun i j h h' => h (hinj h')
  have l0 : G.IsLink (e 0) a (x 0) := hpath 0
  have l1 : G.IsLink (e 1) (x 0) (x 1) := hpath 1
  have l2 : G.IsLink (e 2) (x 1) (x 2) := hpath 2
  have l3 : G.IsLink (e 3) (x 2) (x 3) := hpath 3
  have l4 : G.IsLink (e 4) (x 3) b := hpath 4
  have e01 : e 0 ≠ e 1 := fun h => by simpa using he h
  have e31 : e 3 ≠ e 1 := fun h => by simpa using he h
  have e41 : e 4 ≠ e 1 := fun h => by simpa using he h
  have x01 := hx 0 1 (by decide)
  have x21 := hx 2 1 (by decide)
  have x31 := hx 3 1 (by decide)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · ext w
    simp only [Graph.vertexSet_splitOff, hcover, Set.mem_sdiff, Set.mem_union, Set.mem_range,
      Set.mem_singleton_iff, Fin.exists_fin_succ, Fin.exists_fin_zero, Matrix.cons_val_zero,
      Matrix.cons_val_succ, Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
    constructor
    · rintro ⟨h | rfl | rfl | rfl | rfl | h, hw⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl rfl)
      · exact absurd rfl hw
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      · exact h.elim
    · rintro (h | rfl | rfl | rfl | h)
      · exact ⟨Or.inl h, fun h' => hxV₁ 1 (h' ▸ h)⟩
      · exact ⟨Or.inr (Or.inl rfl), x01⟩
      · exact ⟨Or.inr (Or.inr (Or.inr (Or.inl rfl))), x21⟩
      · exact ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))), x31⟩
      · exact h.elim
  · rw [show ![x 0, x 2, x 3] = x ∘ ![0, 2, 3] by funext i; fin_cases i <;> rfl]
    exact hinj.comp (by decide)
  · intro i; fin_cases i <;> exact hxV₁ _
  · intro i
    fin_cases i
    · exact Or.inl ⟨e01, l0, (hax 1).symm, x01⟩
    · exact Or.inr ⟨rfl, x01, x21, l1.left_mem, l2.right_mem, Or.inl ⟨rfl, rfl⟩⟩
    · exact Or.inl ⟨e31, l3, x21, x31⟩
    · exact Or.inl ⟨e41, l4, x31, (hbx 1).symm⟩
  · intro f u w hf hfe
    rcases hf with ⟨hne, hf, hu, hw⟩ | ⟨rfl, -⟩
    · refine hsep f u w hf (fun i => ?_)
      fin_cases i
      · exact hfe 0
      · exact hne
      · rintro rfl
        rcases hf.eq_and_eq_or_eq_and_eq l2 with ⟨h, -⟩ | ⟨-, h⟩
        · exact hu h
        · exact hw h
      · exact hfe 2
      · exact hfe 3
    · exact absurd rfl (hfe 1)

/-- **The antecedent of the three-body ear is a two-body ear** (`thm:pencil-x0-open-ear-three`):
suppressing `x 1` and relinking `e 1` to `x 0 − x 2` leaves the ear `a − x 0 − x 2 − b` on `V₁`,
with the labels `e 0, e 1, e 3`. -/
theorem splitOff_ear_three {G : Graph α β} {V₁ : Set α} {x : Fin 3 → α} {a b : α}
    {e : Fin 4 → β} (hcover : V(G) = V₁ ∪ Set.range x) (hinj : Function.Injective x)
    (hxV₁ : ∀ i, x i ∉ V₁) (ha : a ∈ V₁) (hb : b ∈ V₁) (hab : a ≠ b)
    (hpath : ∀ i : Fin 4,
      G.IsLink (e i) (pathVertex a x b i.castSucc) (pathVertex a x b i.succ))
    (hsep : ∀ f u w, G.IsLink f u w → (∀ i, f ≠ e i) → u ∈ V₁ ∧ w ∈ V₁) :
    V(G.splitOff (x 1) (x 0) (x 2) (e 1)) = V₁ ∪ Set.range ![x 0, x 2] ∧
      Function.Injective ![x 0, x 2] ∧ (∀ i, ![x 0, x 2] i ∉ V₁) ∧
      (∀ i : Fin 3, (G.splitOff (x 1) (x 0) (x 2) (e 1)).IsLink (![e 0, e 1, e 3] i)
        (pathVertex a ![x 0, x 2] b i.castSucc) (pathVertex a ![x 0, x 2] b i.succ)) ∧
      (∀ f u w, (G.splitOff (x 1) (x 0) (x 2) (e 1)).IsLink f u w →
        (∀ i, f ≠ ![e 0, e 1, e 3] i) → u ∈ V₁ ∧ w ∈ V₁) := by
  have hax : ∀ i, x i ≠ a := fun i h => hxV₁ i (h ▸ ha)
  have hbx : ∀ i, x i ≠ b := fun i h => hxV₁ i (h ▸ hb)
  have he := pathEdge_injective hinj hax hbx hab hpath
  have hx : ∀ i j, i ≠ j → x i ≠ x j := fun i j h h' => h (hinj h')
  have l0 : G.IsLink (e 0) a (x 0) := hpath 0
  have l1 : G.IsLink (e 1) (x 0) (x 1) := hpath 1
  have l2 : G.IsLink (e 2) (x 1) (x 2) := hpath 2
  have l3 : G.IsLink (e 3) (x 2) b := hpath 3
  have e01 : e 0 ≠ e 1 := fun h => by simpa using he h
  have e31 : e 3 ≠ e 1 := fun h => by simpa using he h
  have x01 := hx 0 1 (by decide)
  have x21 := hx 2 1 (by decide)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · ext w
    simp only [Graph.vertexSet_splitOff, hcover, Set.mem_sdiff, Set.mem_union, Set.mem_range,
      Set.mem_singleton_iff, Fin.exists_fin_succ, Fin.exists_fin_zero, Matrix.cons_val_zero,
      Matrix.cons_val_succ, Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
    constructor
    · rintro ⟨h | rfl | rfl | rfl | h, hw⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl rfl)
      · exact absurd rfl hw
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact h.elim
    · rintro (h | rfl | rfl | h)
      · exact ⟨Or.inl h, fun h' => hxV₁ 1 (h' ▸ h)⟩
      · exact ⟨Or.inr (Or.inl rfl), x01⟩
      · exact ⟨Or.inr (Or.inr (Or.inr (Or.inl rfl))), x21⟩
      · exact h.elim
  · rw [show ![x 0, x 2] = x ∘ ![0, 2] by funext i; fin_cases i <;> rfl]
    exact hinj.comp (by decide)
  · intro i; fin_cases i <;> exact hxV₁ _
  · intro i
    fin_cases i
    · exact Or.inl ⟨e01, l0, (hax 1).symm, x01⟩
    · exact Or.inr ⟨rfl, x01, x21, l1.left_mem, l2.right_mem, Or.inl ⟨rfl, rfl⟩⟩
    · exact Or.inl ⟨e31, l3, x21, (hbx 1).symm⟩
  · intro f u w hf hfe
    rcases hf with ⟨hne, hf, hu, hw⟩ | ⟨rfl, -⟩
    · refine hsep f u w hf (fun i => ?_)
      fin_cases i
      · exact hfe 0
      · exact hne
      · rintro rfl
        rcases hf.eq_and_eq_or_eq_and_eq l2 with ⟨h, -⟩ | ⟨-, h⟩
        · exact hu h
        · exact hw h
      · exact hfe 2
    · exact absurd rfl (hfe 1)

/-- **`G[V₁]` sits inside the antecedent**, and **is its subgraph induced on `V₁`**. -/
theorem induce_splitOff_ear {G : Graph α β} {V₁ : Set α} {k : ℕ} {x : Fin k → α}
    (hcover : V(G) = V₁ ∪ Set.range x) (hxV₁ : ∀ i, x i ∉ V₁)
    {v u w : α} {e₀ : β} (hv : v ∈ Set.range x) (hu : u ∉ V₁)
    (he₀ : ∀ y y', G.IsLink e₀ y y' → y ∉ V₁ ∨ y' ∉ V₁) :
    G.induce V₁ ≤ G.splitOff v u w e₀ ∧ (G.splitOff v u w e₀).induce V₁ = G.induce V₁ := by
  have hvV : v ∉ V₁ := by obtain ⟨i, rfl⟩ := hv; exact hxV₁ i
  refine ⟨⟨fun y hy => ⟨hcover ▸ Or.inl hy, fun h => hvV (h ▸ hy)⟩, ?_⟩, ?_⟩
  · rintro f y y' ⟨hf, hy, hy'⟩
    refine Or.inl ⟨?_, hf, fun h => hvV (h ▸ hy), fun h => hvV (h ▸ hy')⟩
    rintro rfl
    rcases he₀ y y' hf with h | h
    exacts [h hy, h hy']
  · refine Graph.ext rfl fun f y y' => ?_
    simp only [Graph.induce_isLink, Graph.splitOff_isLink]
    constructor
    · rintro ⟨⟨hne, hf, -, -⟩ | ⟨-, -, -, -, -, ⟨rfl, -⟩ | ⟨-, rfl⟩⟩, hy, hy'⟩
      · exact ⟨hf, hy, hy'⟩
      · exact absurd hy hu
      · exact absurd hy' hu
    · rintro ⟨hf, hy, hy'⟩
      refine ⟨Or.inl ⟨?_, hf, fun h => hvV (h ▸ hy), fun h => hvV (h ▸ hy')⟩, hy, hy'⟩
      rintro rfl
      rcases he₀ y y' hf with h | h
      exacts [h hy, h hy']

open Classical in
/-- **A selector of `G`, relinked at the new edge, is a selector of the split-off**: if `ends`
orients every link of `G`, then `ends` with `e₀` sent to `(u, w)` orients every link of
`G.splitOff v u w e₀`. -/
theorem _root_.Graph.isLink_update_splitOff {G : Graph α β} {v u w : α} {e₀ : β}
    {ends : β → α × α} (hends : ∀ f p p', G.IsLink f p p' → G.IsLink f (ends f).1 (ends f).2)
    (hl₀ : (G.splitOff v u w e₀).IsLink e₀ u w) (f : β) {p p' : α}
    (hf : (G.splitOff v u w e₀).IsLink f p p') :
    (G.splitOff v u w e₀).IsLink f (Function.update ends e₀ (u, w) f).1
      (Function.update ends e₀ (u, w) f).2 := by
  by_cases hf1 : f = e₀
  · subst hf1
    rw [Function.update_self]
    exact hl₀
  · rw [Function.update_of_ne hf1]
    rcases hf with ⟨-, hf, hp, hp'⟩ | ⟨h, -⟩
    · have hl := hends f p p' hf
      refine Or.inl ⟨hf1, hl, ?_, ?_⟩ <;>
        rcases hl.eq_and_eq_or_eq_and_eq hf with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
        simp only [h1, h2] <;> assumption
    · exact absurd h hf1

end Antecedent

/-! ## The tetrahedron witness -/

/-- **Four points in the tetrahedron witness** (the base point `p_b`, one point over each of
`p_b + (0, 1)` and `p_b + (1, 0)`, and one straight above `p_b`) are independent. -/
theorem linearIndependent_tetra_witness (b₀ b₁ b₂ γ δ : K) :
    LinearIndependent K ![![b₀, b₁ + 1, γ, 1], ![b₀, b₁, b₂ + 1, 1], ![b₀ + 1, b₁, δ, 1],
      ![b₀, b₁, b₂, (1 : K)]] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have h0 := congr_fun hg 0
  have h1 := congr_fun hg 1
  have h2 := congr_fun hg 2
  have h3 := congr_fun hg 3
  simp only [Fin.sum_univ_four, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Matrix.cons_val, Pi.zero_apply] at h0 h1 h2 h3
  have g2 : g 2 = 0 := by linear_combination h0 - b₀ * h3
  have g0 : g 0 = 0 := by linear_combination h1 - b₁ * h3
  have g1 : g 1 = 0 := by
    linear_combination h2 - b₂ * h3 - (γ - b₂) * (h1 - b₁ * h3) - (δ - b₂) * (h0 - b₀ * h3)
  have g3 : g 3 = 0 := by rw [g0, g1, g2] at h3; simpa using h3
  intro i; fin_cases i <;> assumption

/-! ## The base data of the three- and four-body steps -/

open Classical in
/-- **The base data of a short ear step** (`thm:pencil-x0-open-ear-four`, the base data; informal
(MC-180), (MC-181) Steps 1–2). Let `H = G.splitOff v u w e₀` carry an open ear `a − y − b` on
`V₁` with at least two interior bodies, with the same subgraph on `V₁` as `G`, and let the ear data
read the planes at `xf ∈ N_H[a]` and `xl ∈ N_H[b]`. If `G[V₁]` and `H` attain, there are base
data `(q, z₁, la, lb)` with:
* `q` off the given nonzero polynomial `Pm` and admissible for `H`;
* over the picture of every ear datum, `z₁` a height of `G[V₁]` agreeing with the planes `la`,
  `lb` on the closed neighbourhoods of `a`, `b`;
* one ear datum `s₁`, with picture `q`, at which `H`, with the selector `ends` relinked at `e₀`,
  has nonzero hinges and its target rank;
* at every ear datum, the relative screws `ρ` of `G[V₁]` between `a` and `b`, and its target rank,
  in the frameworks of both `G` and `H`. -/
theorem _root_.Graph.exists_earBase_splitOff [Infinite K] [Finite α] {G : Graph α β}
    {V₁ : Set α} {v u w : α} {e₀ : β} {k : ℕ} {y : Fin k → α} {a b : α} {e : Fin (k + 1) → β}
    (hk : 2 ≤ k) (hcover : V(G.splitOff v u w e₀) = V₁ ∪ Set.range y)
    (hinj : Function.Injective y) (hyV₁ : ∀ i, y i ∉ V₁) (ha : a ∈ V₁) (hb : b ∈ V₁)
    (hab : a ≠ b)
    (hpath : ∀ i : Fin (k + 1), (G.splitOff v u w e₀).IsLink (e i)
      (pathVertex a y b i.castSucc) (pathVertex a y b i.succ))
    (hsep : ∀ f p p', (G.splitOff v u w e₀).IsLink f p p' → (∀ i, f ≠ e i) →
      p ∈ V₁ ∧ p' ∈ V₁)
    (hl₀ : (G.splitOff v u w e₀).IsLink e₀ u w)
    (he₀ : ∀ p p', G.IsLink e₀ p p' → p ∉ V₁ ∨ p' ∉ V₁)
    (hle : G.induce V₁ ≤ G.splitOff v u w e₀)
    (hind : (G.splitOff v u w e₀).induce V₁ = G.induce V₁)
    {ends : β → α × α} (hends : ∀ f p p', G.IsLink f p p' → G.IsLink f (ends f).1 (ends f).2)
    {xf xl : α} {X : Set α} (hxf : xf ∈ (G.splitOff v u w e₀).closedNbhd a)
    (hxl : xl ∈ (G.splitOff v u w e₀).closedNbhd b) (hX : Set.range y ⊆ X)
    (h₁ : (G.induce V₁).X0Attains K) (h₂ : (G.splitOff v u w e₀).X0Attains K)
    {Pm : MvPolynomial (α × Fin 2) K} (hPm : Pm ≠ 0) :
    ∃ (q : α × Fin 2 → K) (z₁ : α → K) (la lb : Fin 3 → K) (s₁ : (α × Fin 2) ⊕ α → K)
      (ρ : Submodule K (ScrewSpace K 2)),
      MvPolynomial.eval q Pm ≠ 0 ∧ (G.splitOff v u w e₀).IsAdmissiblePicture q ∧
      earPicture V₁ q s₁ = q ∧
      (Module.finrank K ↥(Submodule.span K (PanelHingeFramework.ofNormals (k := 2)
          (G.splitOff v u w e₀) (Function.update ends e₀ (u, w))
          (earConfig V₁ q z₁ xf xl X la lb s₁)).toBodyHinge.rigidityRows) : ℤ) =
        screwDim 2 * ((V(G.splitOff v u w e₀).ncard : ℤ) - 1) -
          (G.splitOff v u w e₀).deficiency 3 ∧
      (∀ f, (G.splitOff v u w e₀).IsLink f (Function.update ends e₀ (u, w) f).1
          (Function.update ends e₀ (u, w) f).2 →
        (PanelHingeFramework.ofNormals (k := 2) (G.splitOff v u w e₀)
          (Function.update ends e₀ (u, w))
          (earConfig V₁ q z₁ xf xl X la lb s₁)).toBodyHinge.supportExtensor f ≠ 0) ∧
      (∀ s, z₁ ∈ (G.induce V₁).liftingSpace (earPicture V₁ q s)) ∧
      (∀ s, ∀ p ∈ (G.induce V₁).closedNbhd a,
        z₁ p = la ⬝ᵥ pencilPicturePoint (earPicture V₁ q s) p) ∧
      (∀ s, ∀ p ∈ (G.induce V₁).closedNbhd b,
        z₁ p = lb ⬝ᵥ pencilPicturePoint (earPicture V₁ q s) p) ∧
      (∀ s, (⟨G.induce V₁, (PanelHingeFramework.ofNormals (k := 2) G ends
          (earConfig V₁ q z₁ xf xl X la lb s)).toBodyHinge.supportExtensor⟩ :
            BodyHingeFramework K 2 α β).relScrews a b = ρ) ∧
      (∀ s, (⟨(G.splitOff v u w e₀).induce V₁, (PanelHingeFramework.ofNormals (k := 2)
          (G.splitOff v u w e₀) (Function.update ends e₀ (u, w))
          (earConfig V₁ q z₁ xf xl X la lb s)).toBodyHinge.supportExtensor⟩ :
            BodyHingeFramework K 2 α β).relScrews a b = ρ) ∧
      (∀ s, (Module.finrank K ↥(Submodule.span K (⟨G.induce V₁,
          (PanelHingeFramework.ofNormals (k := 2) G ends
            (earConfig V₁ q z₁ xf xl X la lb s)).toBodyHinge.supportExtensor⟩ :
              BodyHingeFramework K 2 α β).rigidityRows) : ℤ) =
        screwDim 2 * ((V₁.ncard : ℤ) - 1) - (G.induce V₁).deficiency 3) ∧
      (∀ s, (Module.finrank K ↥(Submodule.span K (⟨(G.splitOff v u w e₀).induce V₁,
          (PanelHingeFramework.ofNormals (k := 2) (G.splitOff v u w e₀)
            (Function.update ends e₀ (u, w))
            (earConfig V₁ q z₁ xf xl X la lb s)).toBodyHinge.supportExtensor⟩ :
              BodyHingeFramework K 2 α β).rigidityRows) : ℤ) =
        screwDim 2 * ((V₁.ncard : ℤ) - 1) - (G.induce V₁).deficiency 3) := by
  set H := G.splitOff v u w e₀ with hH
  set ends'' := Function.update ends e₀ (u, w) with hends''def
  have hends'' : ∀ f p p', H.IsLink f p p' → H.IsLink f (ends'' f).1 (ends'' f).2 :=
    fun f _ _ hf => G.isLink_update_splitOff hends hl₀ f hf
  have hendsI : ∀ f p p', (G.induce V₁).IsLink f p p' →
      (G.induce V₁).IsLink f (ends f).1 (ends f).2 := by
    intro f p p' hf
    have hl := hends f p p' hf.1
    rcases hl.eq_and_eq_or_eq_and_eq hf.1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨hl, h1 ▸ hf.2.1, h2 ▸ hf.2.2⟩
    · exact ⟨hl, h1 ▸ hf.2.2, h2 ▸ hf.2.1⟩
  have hnot : ∀ f p p', (G.induce V₁).IsLink f p p' → f ≠ e₀ := by
    rintro f p p' ⟨hf, hp, hp'⟩ rfl
    rcases he₀ p p' hf with h | h
    exacts [h hp, h hp']
  -- the picture `q*`, generic for `X₀(G[V₁])` and `X₀(H)`, off `Pm`
  obtain ⟨ends₁, P₁, hends₁, hP₁, hgood₁⟩ := h₁
  obtain ⟨ends₂, P₂, hends₂, hP₂, hgood₂⟩ := h₂
  obtain ⟨q', hq'⟩ := MvPolynomial.exists_eval_ne_zero (mul_ne_zero (mul_ne_zero hP₁ hP₂) hPm)
  rw [map_mul, map_mul] at hq'
  obtain ⟨-, R₁, ⟨z₁', hz₁', hR₁'⟩, hatt₁⟩ :=
    hgood₁ q' (left_ne_zero_of_mul (left_ne_zero_of_mul hq'))
  obtain ⟨hadm₂, R₂, ⟨z₂', hz₂', hR₂'⟩, hatt₂⟩ :=
    hgood₂ q' (right_ne_zero_of_mul (left_ne_zero_of_mul hq'))
  -- the heights `z*`: in `L_H(q*)`, attaining for `H` and, restricted, for `G[V₁]`
  have hex₁ : ∃ z ∈ H.liftingSpace q', MvPolynomial.eval z (restrictPoly V₁ R₁) ≠ 0 := by
    rw [← hind] at hz₁'
    obtain ⟨z, hz, hzr, -⟩ :=
      H.earExtend_mem_liftingSpace hk hcover hinj hyV₁ ha hb hab hpath hsep hadm₂ hz₁' 0
    exact ⟨z, hz, by rwa [eval_restrictPoly, hzr]⟩
  obtain ⟨zs, hzs, hzs₁, hzs₂⟩ := MvPolynomial.exists_mem_eval_ne_zero₂ hex₁ ⟨z₂', hz₂', hR₂'⟩
  rw [eval_restrictPoly] at hzs₁
  set z₁ := Graph.liftingRestrict V₁ zs with hz₁def
  have hz₁ : z₁ ∈ (G.induce V₁).liftingSpace q' := Graph.liftingRestrict_mem_liftingSpace hle hzs
  have hr₁ := hatt₁ z₁ hz₁ hzs₁
  have hr₂ := hatt₂ zs hzs hzs₂
  -- the planes at `a` and `b`
  obtain ⟨la, hla⟩ := hzs.2 a (hcover ▸ Or.inl ha)
  obtain ⟨lb, hlb⟩ := hzs.2 b (hcover ▸ Or.inl hb)
  -- the ear datum `s* = (q*, z*)`
  set cfg := earConfig V₁ q' z₁ xf xl X la lb with hcfgdef
  set sstar : (α × Fin 2) ⊕ α → K := Sum.elim q' zs with hsstar
  have hpicstar : earPicture V₁ q' sstar = q' := by
    funext p; by_cases hp : p.1 ∈ V₁ <;> simp [earPicture, hp, hsstar]
  have hzstar : earHeight V₁ z₁ xf xl X la lb q' zs = zs := by
    funext p
    simp only [earHeight]
    split_ifs with h1 h2 h3 h4
    · simp [hz₁def, Graph.liftingRestrict_apply, h1]
    · subst h2; exact (hla _ hxf).symm
    · subst h3; exact (hlb _ hxl).symm
    · rfl
    · refine (hzs.1 p ?_).symm
      rw [hcover]
      rintro (h | h)
      exacts [h1 h, h4 (hX h)]
  have hcfgstar : cfg sstar = fun p => pencilConfigPoint q' zs p.1 p.2 := by
    funext p
    change pencilConfigPoint (earPicture V₁ q' sstar) (earHeight V₁ z₁ xf xl X la lb
      (earPicture V₁ q' sstar) zs) p.1 p.2 = _
    rw [hpicstar, hzstar]
  -- what the frameworks along the ear data read on `V₁`
  have hcV₁ : ∀ s p, p ∈ V₁ → ∀ j, cfg s (p, j) = pencilConfigPoint q' z₁ p j :=
    fun s p hp j => earConfig_of_mem s hp j
  have hCG : ∀ s f p p', (G.induce V₁).IsLink f p p' →
      (PanelHingeFramework.ofNormals (k := 2) G ends (cfg s)).toBodyHinge.supportExtensor f =
        (PanelHingeFramework.ofNormals (k := 2) G ends
          (cfg sstar)).toBodyHinge.supportExtensor f := by
    intro s f p p' hf
    obtain ⟨-, h1, h2⟩ := hendsI f p p' hf
    simp only [PanelHingeFramework.toBodyHinge_supportExtensor,
      PanelHingeFramework.ofNormals_normal, PanelHingeFramework.ofNormals_ends]
    congr 1 <;> funext j
    · rw [hcV₁ _ _ h1, hcV₁ _ _ h1]
    · rw [hcV₁ _ _ h2, hcV₁ _ _ h2]
  have hC2 : ∀ s f p p', (G.induce V₁).IsLink f p p' →
      (PanelHingeFramework.ofNormals (k := 2) H ends'' (cfg s)).toBodyHinge.supportExtensor f =
        (PanelHingeFramework.ofNormals (k := 2) G ends (cfg s)).toBodyHinge.supportExtensor f := by
    intro s f p p' hf
    simp only [PanelHingeFramework.toBodyHinge_supportExtensor,
      PanelHingeFramework.ofNormals_normal, PanelHingeFramework.ofNormals_ends, hends''def,
      Function.update_of_ne (hnot f p p' hf)]
  have hrk₁ : ∀ s, (Module.finrank K ↥(Submodule.span K (⟨G.induce V₁,
      (PanelHingeFramework.ofNormals (k := 2) G ends (cfg s)).toBodyHinge.supportExtensor⟩ :
        BodyHingeFramework K 2 α β).rigidityRows) : ℤ) =
        screwDim 2 * ((V₁.ncard : ℤ) - 1) - (G.induce V₁).deficiency 3 := by
    intro s
    rw [BodyHingeFramework.finrank_span_rigidityRows_congr (G.induce V₁) (hCG s)]
    have := PanelHingeFramework.finrank_span_rigidityRows_ofNormals_congr (k := 2) (G.induce V₁)
      hendsI hends₁ (q := cfg sstar) (q' := fun p => pencilConfigPoint q' z₁ p.1 p.2)
      (fun w hw j => hcV₁ sstar w hw j)
    change (Module.finrank K ↥(Submodule.span K (PanelHingeFramework.ofNormals (k := 2)
      (G.induce V₁) ends (cfg sstar)).toBodyHinge.rigidityRows) : ℤ) = _
    rw [this, hr₁]
    rfl
  have hpp : ∀ s, ∀ p ∈ V₁,
      pencilPicturePoint (earPicture V₁ q' s) p = pencilPicturePoint q' p := by
    intro s p hp; funext i; fin_cases i <;> simp [pencilPicturePoint, earPicture_of_mem s hp]
  refine ⟨q', z₁, la, lb, sstar,
    (⟨G.induce V₁, (PanelHingeFramework.ofNormals (k := 2) G ends
      (cfg sstar)).toBodyHinge.supportExtensor⟩ : BodyHingeFramework K 2 α β).relScrews a b,
    right_ne_zero_of_mul hq', hadm₂, hpicstar, ?_, ?_, fun s => ?_, fun s p hp => ?_,
    fun s p hp => ?_, fun s => BodyHingeFramework.relScrews_congr (G.induce V₁) (hCG s) a b,
    fun s => ?_, hrk₁, fun s => ?_⟩
  · rw [← hcfgdef, hcfgstar, PanelHingeFramework.finrank_span_rigidityRows_ofNormals_congr (k := 2)
      H hends'' hends₂ (fun _ _ _ => rfl)]
    exact hr₂
  · rw [← hcfgdef, hcfgstar]
    exact fun f hf => hadm₂.supportExtensor_ne_zero hends'' zs hf
  · rw [Graph.liftingSpace_congr (G := G.induce V₁) (q := earPicture V₁ q' s) (q' := q')
      (fun w hw i => earPicture_of_mem s hw i)]
    exact hz₁
  · have hpV : p ∈ V₁ := Graph.closedNbhd_subset_vertexSet ha hp
    have hp'' : p ∈ H.closedNbhd a := by
      rcases hp with rfl | ⟨f, hf⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨f, hf.of_le hle⟩
    rw [hpp s p hpV, ← hla p hp'']
    simp [hz₁def, Graph.liftingRestrict_apply, hpV]
  · have hpV : p ∈ V₁ := Graph.closedNbhd_subset_vertexSet hb hp
    have hp'' : p ∈ H.closedNbhd b := by
      rcases hp with rfl | ⟨f, hf⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨f, hf.of_le hle⟩
    rw [hpp s p hpV, ← hlb p hp'']
    simp [hz₁def, Graph.liftingRestrict_apply, hpV]
  · rw [hind]
    exact BodyHingeFramework.relScrews_congr (G.induce V₁)
      (fun f p p' hf => (hC2 s f p p' hf).trans (hCG s f p p' hf)) a b
  · rw [hind, BodyHingeFramework.finrank_span_rigidityRows_congr (G.induce V₁) (hC2 s)]
    exact hrk₁ s

/-! ## The open ear with four interior bodies -/

open Classical in
/-- **(MC-180), the open ear with four interior bodies** (`thm:pencil-x0-open-ear-four`). Let `G`
satisfy (H), with an open ear `a − x 0 − x 1 − x 2 − x 3 − b` on `V₁` whose ends may be adjacent,
and let `G″ = G.splitOff (x 1) (x 0) (x 2) (e 1)` be `G` with `x 1` suppressed, the freed label
`e 1` relinked to `x 0 − x 2`. If `X₀(G[V₁])` and `X₀(G″)` attain, `X₀(G)` attains. The base data
are `Graph.exists_earBase_splitOff`'s; `x 1` is put back at the point of `exists_insertion_four`;
the count is `Graph.splitOff_deficiency_le_of_eq_left` and `Graph.deficiency_induce_add_le_of_ear`.
-/
theorem _root_.Graph.X0Attains.of_openEar_four [Infinite K] [Finite α] [Finite β]
    {G : Graph α β} (hG : G.IsX0Graph) {V₁ : Set α} {x : Fin 4 → α} {a b : α}
    {e : Fin 5 → β} (hcover : V(G) = V₁ ∪ Set.range x) (hinj : Function.Injective x)
    (hxV₁ : ∀ i, x i ∉ V₁) (ha : a ∈ V₁) (hb : b ∈ V₁) (hab : a ≠ b)
    (hpath : ∀ i : Fin 5,
      G.IsLink (e i) (pathVertex a x b i.castSucc) (pathVertex a x b i.succ))
    (hsep : ∀ f u w, G.IsLink f u w → (∀ i, f ≠ e i) → u ∈ V₁ ∧ w ∈ V₁)
    (h₁ : (G.induce V₁).X0Attains K)
    (h₂ : (G.splitOff (x 1) (x 0) (x 2) (e 1)).X0Attains K) : G.X0Attains K := by
  have hV : V(G).Nonempty := hG.connected.nonempty
  have : Inhabited α := ⟨a⟩
  have hax : ∀ i, x i ≠ a := fun i h => hxV₁ i (h ▸ ha)
  have hbx : ∀ i, x i ≠ b := fun i h => hxV₁ i (h ▸ hb)
  have hx : ∀ i j, i ≠ j → x i ≠ x j := fun i j h h' => h (hinj h')
  have l0 : G.IsLink (e 0) a (x 0) := hpath 0
  have l1 : G.IsLink (e 1) (x 0) (x 1) := hpath 1
  have l2 : G.IsLink (e 2) (x 1) (x 2) := hpath 2
  have l3 : G.IsLink (e 3) (x 2) (x 3) := hpath 3
  have l4 : G.IsLink (e 4) (x 3) b := hpath 4
  have x01 := hx 0 1 (by decide)
  have x02 := hx 0 2 (by decide)
  have x03 := hx 0 3 (by decide)
  have x12 := hx 1 2 (by decide)
  have x13 := hx 1 3 (by decide)
  have x23 := hx 2 3 (by decide)
  -- the antecedent `G″ = G′ + (a − x 0 − x 2 − x 3 − b)`
  set G'' := G.splitOff (x 1) (x 0) (x 2) (e 1) with hG''
  set x'' : Fin 3 → α := ![x 0, x 2, x 3] with hx''
  set e'' : Fin 4 → β := ![e 0, e 1, e 3, e 4] with he''
  obtain ⟨hcover'', hinj'', hxV₁'', hpath'', hsep''⟩ :=
    splitOff_ear_four hcover hinj hxV₁ ha hb hab hpath hsep
  have he₁ : ∀ y y', G.IsLink (e 1) y y' → y ∉ V₁ ∨ y' ∉ V₁ := by
    intro y y' h
    rcases h.eq_and_eq_or_eq_and_eq l1 with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact Or.inl (hxV₁ 0)
    · exact Or.inl (hxV₁ 1)
  obtain ⟨hle₁'', hind⟩ := induce_splitOff_ear (x := x) (e₀ := e 1) (w := x 2) hcover hxV₁
    ⟨1, rfl⟩ (hxV₁ 0) he₁
  -- Steps 1–2: the main polynomial of `G`, the base data, and the selectors
  obtain ⟨Pm, hPm, hmain⟩ := G.exists_mvPolynomial_isMainPicture (K := K)
    hG.simple.toLoopless hG.three_le_ncard_closedNbhd
  set ends := G.endsOf with hendsdef
  have hends : ∀ f u w, G.IsLink f u w → G.IsLink f (ends f).1 (ends f).2 :=
    fun f _ _ hf => G.isLink_endsOf hf.edge_mem
  set ends'' := Function.update ends (e 1) (x 0, x 2) with hends''def
  have hends'' : ∀ f u w, G''.IsLink f u w → G''.IsLink f (ends'' f).1 (ends'' f).2 :=
    fun f _ _ hf => G.isLink_update_splitOff hends (hpath'' 1) f hf
  obtain ⟨q', z₁, la, lb, sstar, ρM, hqm', hadm₂, hpicstar, hrk₂, hne₂, hz₁s, hlas, hlbs, hρG,
      hρ2, hrk₁, hrk₁''⟩ :=
    Graph.exists_earBase_splitOff (xf := x 0) (xl := x 3) (X := Set.range x) (by norm_num)
      hcover'' hinj'' hxV₁'' ha hb hab hpath'' hsep'' (hpath'' 1) he₁ hle₁'' hind hends
      (Or.inr ⟨e 0, hpath'' 0⟩) (Or.inr ⟨e 4, (hpath'' 3).symm⟩)
      (by rintro _ ⟨i, rfl⟩; fin_cases i <;> exact ⟨_, rfl⟩) h₁ h₂ hPm
  set cfg := earConfig V₁ q' z₁ (x 0) (x 3) (Set.range x) la lb with hcfgdef
  set P := earPointPoly (K := K) V₁ q' z₁ (x 0) (x 3) (Set.range x) la lb with hPdef
  have hPc : ∀ s, (fun p => MvPolynomial.eval s (P p)) = cfg s :=
    fun s => funext (eval_earPointPoly V₁ q' z₁ (x 0) (x 3) (Set.range x) la lb s)
  have hcV₁ : ∀ s w, w ∈ V₁ → ∀ j, cfg s (w, j) = pencilConfigPoint q' z₁ w j :=
    fun s w hw j => earConfig_of_mem s hw j
  set ρJ := ρM.map (screwComplementIso (K := K)).symm.toLinearMap with hρJ
  -- the three polynomial conditions on the ear data of `G″`
  set N'' := (screwDim 2 * ((V(G'').ncard : ℤ) - 1) - G''.deficiency 3).toNat with hN''def
  have hN'' : N'' ≤ Module.finrank K (Submodule.span K (PanelHingeFramework.ofNormals (k := 2)
      G'' ends'' (fun p => MvPolynomial.eval sstar (P p))).toBodyHinge.rigidityRows) := by
    rw [hPc]
    exact Int.toNat_le.mpr hrk₂.symm.le
  have hne'' : ∀ f, G''.IsLink f (ends'' f).1 (ends'' f).2 →
      (PanelHingeFramework.ofNormals (k := 2) G'' ends''
        (fun p => MvPolynomial.eval sstar (P p))).toBodyHinge.supportExtensor f ≠ 0 := by
    rw [hPc]
    exact hne₂
  obtain ⟨Q₂, hQ₂₀, hQ₂⟩ := exists_mvPolynomial_le_finrank_ofNormals_bind G'' ends'' hends'' P
    hne'' hN''
  obtain ⟨Pa, hPa₀, hPa⟩ := hadm₂.exists_mvPolynomial
  have hPa'₀ : MvPolynomial.eval sstar (MvPolynomial.bind₁ (earPicturePoly V₁ q') Pa) ≠ 0 := by
    rwa [eval_bind₁_earPicturePoly, hpicstar]
  -- the tetrahedron `x 0, x 2, x 3, b` spans at one ear datum
  set ut : Fin 6 → α := fun i => ![x 0, x 2, x 3, b] (tetA i) with hut
  set wt : Fin 6 → α := fun i => ![x 0, x 2, x 3, b] (tetB i) with hwt
  have htet₀ : ∃ stet : (α × Fin 2) ⊕ α → K, 6 ≤ Module.finrank K ↥((⊥ : Submodule K
      (ScrewSpace K 2)) ⊔ Submodule.span K (Set.range fun i =>
        pointJoin (fun j => MvPolynomial.eval stet (P (ut i, j)))
          (fun j => MvPolynomial.eval stet (P (wt i, j))))) := by
    set b₀ := q' (b, 0)
    set b₁ := q' (b, 1)
    set stet : (α × Fin 2) ⊕ α → K := Sum.elim
      (fun p => if p.1 = x 0 then ![b₀, b₁ + 1] p.2 else if p.1 = x 2 then ![b₀, b₁] p.2
        else if p.1 = x 3 then ![b₀ + 1, b₁] p.2 else 0)
      (fun w => if w = x 2 then z₁ b + 1 else 0) with hstet
    refine ⟨stet, ?_⟩
    have hp0 : (fun j => cfg stet (x 0, j)) =
        ![b₀, b₁ + 1, la ⬝ᵥ ![b₀, b₁ + 1, 1], 1] := by
      rw [earConfig_first stet (hxV₁ 0)]
      funext j; fin_cases j <;> simp [hstet, liftPlane]
    have hp2 : (fun j => cfg stet (x 2, j)) = ![b₀, b₁, z₁ b + 1, 1] := by
      rw [earConfig_of_mem_X stet (hxV₁ 2) x02.symm x23 (Set.mem_range_self 2)]
      funext j; fin_cases j <;> simp [hstet, x02.symm]
    have hp3 : (fun j => cfg stet (x 3, j)) =
        ![b₀ + 1, b₁, lb ⬝ᵥ ![b₀ + 1, b₁, 1], 1] := by
      rw [earConfig_last stet (hxV₁ 3) x03.symm]
      funext j; fin_cases j <;> simp [hstet, liftPlane, x03.symm, x23.symm]
    have hpb : (fun j => cfg stet (b, j)) = ![b₀, b₁, z₁ b, 1] := by
      funext j; rw [hcV₁ stet b hb]
      fin_cases j <;> simp [pencilConfigPoint, b₀, b₁]
    have hli : LinearIndependent K ![fun j => cfg stet (x 0, j), fun j => cfg stet (x 2, j),
        fun j => cfg stet (x 3, j), fun j => cfg stet (b, j)] := by
      rw [hp0, hp2, hp3, hpb]
      exact linearIndependent_tetra_witness b₀ b₁ (z₁ b) _ _
    have hpts : ∀ m : Fin 4, (fun j => MvPolynomial.eval stet (P (![x 0, x 2, x 3, b] m, j))) =
        ![fun j => cfg stet (x 0, j), fun j => cfg stet (x 2, j),
          fun j => cfg stet (x 3, j), fun j => cfg stet (b, j)] m := by
      intro m
      funext j
      rw [show MvPolynomial.eval stet (P (![x 0, x 2, x 3, b] m, j)) =
        cfg stet (![x 0, x 2, x 3, b] m, j) from congrFun (hPc stet) _]
      fin_cases m <;> rfl
    have hfam : (fun i => pointJoin (fun j => MvPolynomial.eval stet (P (ut i, j)))
        (fun j => MvPolynomial.eval stet (P (wt i, j)))) = fun i =>
          pointJoin (![fun j => cfg stet (x 0, j), fun j => cfg stet (x 2, j),
            fun j => cfg stet (x 3, j), fun j => cfg stet (b, j)] (tetA i))
          (![fun j => cfg stet (x 0, j), fun j => cfg stet (x 2, j),
            fun j => cfg stet (x 3, j), fun j => cfg stet (b, j)] (tetB i)) := by
      funext i
      simp only [hut, hwt]
      rw [hpts, hpts]
    rw [hfam, span_pointJoin_tetra_eq_top hli, bot_sup_eq, finrank_top, finrank_screwSpace_two]
  obtain ⟨stet, hstet⟩ := htet₀
  obtain ⟨Qt, hQt₀, hQt⟩ := exists_mvPolynomial_le_finrank_sup_span_pointJoin ⊥ P ut wt hstet
  have hne0 : ∀ {Q : MvPolynomial ((α × Fin 2) ⊕ α) K} {s}, MvPolynomial.eval s Q ≠ 0 → Q ≠ 0 :=
    fun h hQ => h (by rw [hQ, map_zero])
  -- Round 1: a common non-root `y` of the three
  obtain ⟨sy, hsy₂, hsya, hsyt⟩ := MvPolynomial.exists_eval_ne_zero₃ (hne0 hQ₂₀) (hne0 hPa'₀)
    (hne0 hQt₀)
  have hrank'' := hQ₂ sy hsy₂
  rw [hPc] at hrank''
  rw [eval_bind₁_earPicturePoly] at hsya
  have hadmy := hPa _ hsya
  have htety := hQt sy hsyt
  -- the points of `G″`'s configuration `y`
  set pt : ((α × Fin 2) ⊕ α → K) → α → Fin 4 → K := fun s w j => cfg s (w, j) with hpt
  have hevpt : ∀ s w, (fun j => MvPolynomial.eval s (P (w, j))) = pt s w :=
    fun s w => funext fun j => congrFun (hPc s) (w, j)
  have hpt3 : ∀ s w, pt s w 3 = 1 := fun s w => rfl
  -- Step 3 at `G″`: `dim W ≥ 4 + f − def(G″)`
  have hC'' : ∀ i, (PanelHingeFramework.ofNormals (k := 2) G'' ends''
      (cfg sy)).toBodyHinge.supportExtensor (e'' i) ≠ 0 :=
    fun i => hadmy.supportExtensor_ne_zero hends'' _ (hpath'' i)
  have hear'' : (Module.finrank K ↥(Submodule.span K (PanelHingeFramework.ofNormals (k := 2) G''
      ends'' (cfg sy)).toBodyHinge.rigidityRows) : ℤ)
      = (Module.finrank K ↥(Submodule.span K (⟨G''.induce V₁, (PanelHingeFramework.ofNormals
            (k := 2) G'' ends'' (cfg sy)).toBodyHinge.supportExtensor⟩ :
              BodyHingeFramework K 2 α β).rigidityRows) : ℤ)
        + ((screwDim 2 : ℤ) - 1) * (3 + 1)
        + (Module.finrank K ↥((⟨G''.induce V₁, (PanelHingeFramework.ofNormals (k := 2) G'' ends''
              (cfg sy)).toBodyHinge.supportExtensor⟩ : BodyHingeFramework K 2 α β).relScrews a b
            ⊔ Submodule.span K (Set.range ((PanelHingeFramework.ofNormals (k := 2) G'' ends''
              (cfg sy)).toBodyHinge.supportExtensor ∘ e''))) : ℤ)
        - (screwDim 2 : ℤ) :=
    BodyHingeFramework.finrank_span_rigidityRows_ear_eq _ hinj'' hxV₁'' ha hb hab hpath'' hsep''
      hC''
  rw [hrk₁'' sy, hρ2 sy, span_supportExtensor_comp_eq_map_pointJoin hends'' (cfg sy) e''
    (fun i => pathVertex a x'' b i.castSucc) (fun i => pathVertex a x'' b i.succ) hpath'',
    finrank_sup_map_screwComplementIso] at hear''
  have hjoins'' : (fun i : Fin 4 => pointJoin (fun j => cfg sy (pathVertex a x'' b i.castSucc, j))
      (fun j => cfg sy (pathVertex a x'' b i.succ, j))) = ![pointJoin (pt sy a) (pt sy (x 0)),
        pointJoin (pt sy (x 0)) (pt sy (x 2)), pointJoin (pt sy (x 2)) (pt sy (x 3)),
        pointJoin (pt sy (x 3)) (pt sy b)] := by
    funext i; fin_cases i <;> rfl
  have hset'' : Set.range ![pointJoin (pt sy a) (pt sy (x 0)),
        pointJoin (pt sy (x 0)) (pt sy (x 2)), pointJoin (pt sy (x 2)) (pt sy (x 3)),
        pointJoin (pt sy (x 3)) (pt sy b)] = {pointJoin (pt sy a) (pt sy (x 0)),
        pointJoin (pt sy (x 0)) (pt sy (x 2)), pointJoin (pt sy (x 2)) (pt sy (x 3)),
        pointJoin (pt sy (x 3)) (pt sy b)} := by
    simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rw [hjoins'', hset''] at hear''
  -- the tetrahedron at `y`
  have htet' : Submodule.span K (Set.range fun i =>
      pointJoin (![pt sy (x 0), pt sy (x 2), pt sy (x 3), pt sy b] (tetA i))
        (![pt sy (x 0), pt sy (x 2), pt sy (x 3), pt sy b] (tetB i))) = ⊤ := by
    have hfam : (fun i => pointJoin (fun j => MvPolynomial.eval sy (P (ut i, j)))
        (fun j => MvPolynomial.eval sy (P (wt i, j)))) = fun i =>
          pointJoin (![pt sy (x 0), pt sy (x 2), pt sy (x 3), pt sy b] (tetA i))
            (![pt sy (x 0), pt sy (x 2), pt sy (x 3), pt sy b] (tetB i)) := by
      have hpts : ∀ m : Fin 4, pt sy (![x 0, x 2, x 3, b] m) =
          ![pt sy (x 0), pt sy (x 2), pt sy (x 3), pt sy b] m := by
        intro m; fin_cases m <;> rfl
      funext i
      rw [hevpt, hevpt]
      simp only [hut, hwt]
      rw [hpts, hpts]
    rw [hfam, bot_sup_eq] at htety
    refine Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le _) ?_)
    rw [finrank_screwSpace_two]; exact htety
  obtain ⟨x₂, hx₂3, hins⟩ := exists_insertion_four ρJ (pt sy a) (pt sy (x 0)) (pt sy (x 2))
    (pt sy (x 3)) (pt sy b) (hpt3 _ _) (hpt3 _ _) htet'
  -- the counts
  set f₁ := (G.induce V₁).deficiency 3 with hf₁
  set dG := G.deficiency 3 with hdG
  set d'' := G''.deficiency 3 with hd''
  have hdisj : Disjoint V₁ (Set.range x) := by
    refine Set.disjoint_left.mpr ?_
    rintro _ h ⟨i, rfl⟩
    exact hxV₁ i h
  have hcount : (V(G).ncard : ℤ) = V₁.ncard + 4 := by
    rw [hcover, Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _),
      Set.ncard_range_of_injective hinj, Nat.card_eq_fintype_card, Fintype.card_fin]
    push_cast; ring
  have hcount'' : (V(G'').ncard : ℤ) = V₁.ncard + 3 := by
    have hdisj'' : Disjoint V₁ (Set.range x'') := by
      refine Set.disjoint_left.mpr ?_
      rintro _ h ⟨i, rfl⟩
      exact hxV₁'' i h
    rw [hcover'', Set.ncard_union_eq hdisj'' (Set.toFinite _) (Set.toFinite _),
      Set.ncard_range_of_injective hinj'', Nat.card_eq_fintype_card, Fintype.card_fin]
    push_cast; ring
  have hdeg2 : ∀ e' y, G.IsLink e' (x 1) y → e' = e 1 ∨ e' = e 2 := by
    intro e' y hl
    by_cases h : ∃ i, e' = e i
    · obtain ⟨i, rfl⟩ := h
      fin_cases i
      · rcases hl.eq_and_eq_or_eq_and_eq l0 with ⟨h1, -⟩ | ⟨h1, -⟩
        exacts [absurd h1 (hax 1), absurd h1 x01.symm]
      · exact Or.inl rfl
      · exact Or.inr rfl
      · rcases hl.eq_and_eq_or_eq_and_eq l3 with ⟨h1, -⟩ | ⟨h1, -⟩
        exacts [absurd h1 x12, absurd h1 x13]
      · rcases hl.eq_and_eq_or_eq_and_eq l4 with ⟨h1, -⟩ | ⟨h1, -⟩
        exacts [absurd h1 x13, absurd h1 (hbx 1)]
    · exact absurd (hsep e' _ _ hl (fun i h' => h ⟨i, h'⟩)).1 (hxV₁ 1)
  have hdef'' : d'' ≤ dG := Graph.splitOff_deficiency_le_of_eq_left (n := 3) (by decide)
    x01 x12.symm (fun h => by simpa using pathEdge_injective hinj hax hbx hab hpath h) l1.symm l2
    hdeg2
  have hdefG : f₁ + 4 + 1 - (Graph.bodyBarDim 3 : ℤ) ≤ dG :=
    Graph.deficiency_induce_add_le_of_ear (n := 3) (k := 4) (by decide) (by omega) hcover hinj hxV₁
      ha hb hpath hsep
  have hs6 : (screwDim 2 : ℤ) = 6 := rfl
  have hb6 : (Graph.bodyBarDim 3 : ℤ) = 6 := rfl
  -- `dim W ≥ 4 + f − def(G″)`
  have hW : 4 + f₁ - d'' ≤ (Module.finrank K ↥(ρJ ⊔ Submodule.span K
      {pointJoin (pt sy a) (pt sy (x 0)), pointJoin (pt sy (x 0)) (pt sy (x 2)),
        pointJoin (pt sy (x 2)) (pt sy (x 3)), pointJoin (pt sy (x 3)) (pt sy b)}) : ℤ) := by
    have h1 : screwDim 2 * ((V(G'').ncard : ℤ) - 1) - d'' ≤
        (Module.finrank K ↥(Submodule.span K (PanelHingeFramework.ofNormals (k := 2) G'' ends''
          (cfg sy)).toBodyHinge.rigidityRows) : ℤ) :=
      (Int.self_le_toNat _).trans (by exact_mod_cast hrank'')
    rw [hear'', hcount''] at h1
    rw [hs6] at h1
    linarith
  -- Step 3: put `x 1` back at `x₂`
  set st := Function.update (Function.update (Function.update sy (Sum.inl (x 1, 0)) (x₂ 0))
    (Sum.inl (x 1, 1)) (x₂ 1)) (Sum.inr (x 1)) (x₂ 2) with hst
  have hpt1 : pt st (x 1) = x₂ := by
    change (fun j => cfg st (x 1, j)) = x₂
    rw [earConfig_of_mem_X st (hxV₁ 1) x01.symm x13 (Set.mem_range_self 1)]
    funext j; fin_cases j <;> simp [hst, hx₂3]
  have hptne : ∀ w, w ≠ x 1 → pt st w = pt sy w := by
    intro w hw
    funext j
    exact earConfig_congr (fun i => by simp [hst, hw]) (by simp [hst, hw]) j
  have hjoinsG : (fun i : Fin 5 => pointJoin (pt st (pathVertex a x b i.castSucc))
      (pt st (pathVertex a x b i.succ))) = ![pointJoin (pt sy a) (pt sy (x 0)),
        pointJoin (pt sy (x 0)) x₂, pointJoin x₂ (pt sy (x 2)),
        pointJoin (pt sy (x 2)) (pt sy (x 3)), pointJoin (pt sy (x 3)) (pt sy b)] := by
    have ha1 : a ≠ x 1 := (hax 1).symm
    have hb1 : b ≠ x 1 := (hbx 1).symm
    funext i
    fin_cases i
    · change pointJoin (pt st a) (pt st (x 0)) = _
      rw [hptne _ ha1, hptne _ x01]; rfl
    · change pointJoin (pt st (x 0)) (pt st (x 1)) = _
      rw [hptne _ x01, hpt1]; rfl
    · change pointJoin (pt st (x 1)) (pt st (x 2)) = _
      rw [hpt1, hptne _ x12.symm]; rfl
    · change pointJoin (pt st (x 2)) (pt st (x 3)) = _
      rw [hptne _ x12.symm, hptne _ x13.symm]; rfl
    · change pointJoin (pt st (x 3)) (pt st b) = _
      rw [hptne _ x13.symm, hptne _ hb1]; rfl
  have hsetG : Set.range ![pointJoin (pt sy a) (pt sy (x 0)),
        pointJoin (pt sy (x 0)) x₂, pointJoin x₂ (pt sy (x 2)),
        pointJoin (pt sy (x 2)) (pt sy (x 3)), pointJoin (pt sy (x 3)) (pt sy b)] =
      {pointJoin (pt sy a) (pt sy (x 0)),
        pointJoin (pt sy (x 0)) x₂, pointJoin x₂ (pt sy (x 2)),
        pointJoin (pt sy (x 2)) (pt sy (x 3)), pointJoin (pt sy (x 3)) (pt sy b)} := by
    simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  -- the target `n₀ = 5 + f − def(G)` is met at `st`
  set n₀ := (5 + f₁ - dG).toNat with hn₀
  have hNt : n₀ ≤ Module.finrank K ↥(ρJ ⊔ Submodule.span K (Set.range fun i : Fin 5 =>
      pointJoin (fun j => MvPolynomial.eval st (P (pathVertex a x b i.castSucc, j)))
        (fun j => MvPolynomial.eval st (P (pathVertex a x b i.succ, j))))) := by
    rw [show (fun i : Fin 5 =>
        pointJoin (fun j => MvPolynomial.eval st (P (pathVertex a x b i.castSucc, j)))
          (fun j => MvPolynomial.eval st (P (pathVertex a x b i.succ, j)))) =
        fun i => pointJoin (pt st (pathVertex a x b i.castSucc)) (pt st (pathVertex a x b i.succ))
      from funext fun i => by rw [hevpt, hevpt]]
    rw [hjoinsG, hsetG]
    refine le_trans ?_ hins
    rw [le_min_iff]
    constructor
    · refine Int.toNat_le.mpr ?_
      push_cast
      linarith
    · refine Int.toNat_le.mpr ?_
      push_cast
      rw [hb6] at hdefG
      linarith
  obtain ⟨Qs, hQs₀, hQs⟩ := exists_mvPolynomial_le_finrank_sup_span_pointJoin ρJ P
    (fun i : Fin 5 => pathVertex a x b i.castSucc) (fun i => pathVertex a x b i.succ) hNt
  have hPm'₀ : MvPolynomial.eval sstar (MvPolynomial.bind₁ (earPicturePoly V₁ q') Pm) ≠ 0 := by
    rwa [eval_bind₁_earPicturePoly, hpicstar]
  -- Round 2: a common non-root, main for `G`
  obtain ⟨s₀, hs₀a, hs₀b⟩ := MvPolynomial.exists_eval_ne_zero₂ (hne0 hQs₀) (hne0 hPm'₀)
  rw [eval_bind₁_earPicturePoly] at hs₀b
  have hqmain₀ := hmain _ hs₀b
  have hz₀ := Graph.earHeight_mem_liftingSpace (k := 4) (by norm_num) hcover hinj hxV₁ ha hb hab
    hpath hsep hqmain₀.1 (hz₁s s₀) (hlas s₀) (hlbs s₀) (fun w => s₀ (Sum.inr w))
  -- the ear rank law at `G`
  have hC : ∀ i, (PanelHingeFramework.ofNormals (k := 2) G ends
      (cfg s₀)).toBodyHinge.supportExtensor (e i) ≠ 0 :=
    fun i => hqmain₀.1.supportExtensor_ne_zero hends _ (hpath i)
  have hear : (Module.finrank K ↥(Submodule.span K (PanelHingeFramework.ofNormals (k := 2) G ends
      (cfg s₀)).toBodyHinge.rigidityRows) : ℤ)
      = (Module.finrank K ↥(Submodule.span K (⟨G.induce V₁, (PanelHingeFramework.ofNormals
            (k := 2) G ends (cfg s₀)).toBodyHinge.supportExtensor⟩ :
              BodyHingeFramework K 2 α β).rigidityRows) : ℤ)
        + ((screwDim 2 : ℤ) - 1) * (4 + 1)
        + (Module.finrank K ↥((⟨G.induce V₁, (PanelHingeFramework.ofNormals (k := 2) G ends
              (cfg s₀)).toBodyHinge.supportExtensor⟩ : BodyHingeFramework K 2 α β).relScrews a b
            ⊔ Submodule.span K (Set.range ((PanelHingeFramework.ofNormals (k := 2) G ends
              (cfg s₀)).toBodyHinge.supportExtensor ∘ e))) : ℤ)
        - (screwDim 2 : ℤ) :=
    BodyHingeFramework.finrank_span_rigidityRows_ear_eq _ hinj hxV₁ ha hb hab hpath hsep hC
  rw [hrk₁ s₀, hρG s₀, span_supportExtensor_comp_eq_map_pointJoin hends (cfg s₀) e
    (fun i => pathVertex a x b i.castSucc) (fun i => pathVertex a x b i.succ) hpath,
    finrank_sup_map_screwComplementIso] at hear
  have hspan₀ := hQs s₀ hs₀a
  rw [show (fun i : Fin 5 =>
      pointJoin (fun j => MvPolynomial.eval s₀ (P (pathVertex a x b i.castSucc, j)))
        (fun j => MvPolynomial.eval s₀ (P (pathVertex a x b i.succ, j)))) =
      fun i => pointJoin (pt s₀ (pathVertex a x b i.castSucc)) (pt s₀ (pathVertex a x b i.succ))
    from funext fun i => by rw [hevpt, hevpt]] at hspan₀
  refine Graph.x0Attains_of_exists hV ends hends hqmain₀ hz₀ ?_
  change _ ≤ (Module.finrank K ↥(Submodule.span K (PanelHingeFramework.ofNormals (k := 2) G ends
    (cfg s₀)).toBodyHinge.rigidityRows) : ℤ)
  rw [hear, hcount, hs6]
  have h₀ : ((5 + f₁ - dG : ℤ)) ≤ (n₀ : ℤ) := Int.self_le_toNat _
  have h₁ : (n₀ : ℤ) ≤ (Module.finrank K ↥(ρJ ⊔ Submodule.span K (Set.range fun i : Fin 5 =>
      pointJoin (pt s₀ (pathVertex a x b i.castSucc)) (pt s₀ (pathVertex a x b i.succ)))) : ℤ) := by
    exact_mod_cast hspan₀
  change _ ≤ _ + _ + (Module.finrank K ↥(ρJ ⊔ Submodule.span K (Set.range fun i : Fin 5 =>
      pointJoin (pt s₀ (pathVertex a x b i.castSucc)) (pt s₀ (pathVertex a x b i.succ)))) : ℤ) - _
  linarith

/-! ## The open ear with three interior bodies -/

open Classical in
/-- **(MC-181), the open ear with three interior bodies** (`thm:pencil-x0-open-ear-three`). Let
`G` satisfy (H), with an open ear `a − x 0 − x 1 − x 2 − b` on `V₁` whose ends may be adjacent, and
let `G″ = G.splitOff (x 1) (x 0) (x 2) (e 1)` be `G` with `x 1` suppressed, the freed label `e 1`
relinked to `x 0 − x 2`. If `X₀(G[V₁])` and `X₀(G″)` attain, `X₀(G)` attains. The base data are
`Graph.exists_earBase_splitOff`'s, with `G″`'s ear `a − x 0 − x 2 − b`. Before the ear data, the
relative screws `ρ` either all pair to zero with every line joining the planes at `a` and `b`
(`not_star_sup_star_le_of_klein`), or one, `c`, does not; then `⟨c, y₁ ∧ y₃⟩ ≠ 0` is a further
open condition on the ear data, a span bound against the kernel of `⟨c, ·⟩` certified at an affine
pair (`exists_klein_liftPlane_affine_ne_zero`), under which a span holding both stars is `Λ²K⁴`
(`eq_top_of_star_sup_star_le`). `x 1` is put back at the point of `exists_insertion_three`; the
count is `Graph.splitOff_deficiency_le_of_eq_left` and `Graph.deficiency_induce_add_le_of_ear`. -/
theorem _root_.Graph.X0Attains.of_openEar_three [Infinite K] [Finite α] [Finite β]
    {G : Graph α β} (hG : G.IsX0Graph) {V₁ : Set α} {x : Fin 3 → α} {a b : α}
    {e : Fin 4 → β} (hcover : V(G) = V₁ ∪ Set.range x) (hinj : Function.Injective x)
    (hxV₁ : ∀ i, x i ∉ V₁) (ha : a ∈ V₁) (hb : b ∈ V₁) (hab : a ≠ b)
    (hpath : ∀ i : Fin 4,
      G.IsLink (e i) (pathVertex a x b i.castSucc) (pathVertex a x b i.succ))
    (hsep : ∀ f u w, G.IsLink f u w → (∀ i, f ≠ e i) → u ∈ V₁ ∧ w ∈ V₁)
    (h₁ : (G.induce V₁).X0Attains K)
    (h₂ : (G.splitOff (x 1) (x 0) (x 2) (e 1)).X0Attains K) : G.X0Attains K := by
  have hV : V(G).Nonempty := hG.connected.nonempty
  have : Inhabited α := ⟨a⟩
  have hax : ∀ i, x i ≠ a := fun i h => hxV₁ i (h ▸ ha)
  have hbx : ∀ i, x i ≠ b := fun i h => hxV₁ i (h ▸ hb)
  have hx : ∀ i j, i ≠ j → x i ≠ x j := fun i j h h' => h (hinj h')
  have l0 : G.IsLink (e 0) a (x 0) := hpath 0
  have l1 : G.IsLink (e 1) (x 0) (x 1) := hpath 1
  have l2 : G.IsLink (e 2) (x 1) (x 2) := hpath 2
  have l3 : G.IsLink (e 3) (x 2) b := hpath 3
  have x01 := hx 0 1 (by decide)
  have x02 := hx 0 2 (by decide)
  have x12 := hx 1 2 (by decide)
  -- the antecedent `G″ = G′ + (a − x 0 − x 2 − b)`
  set G'' := G.splitOff (x 1) (x 0) (x 2) (e 1) with hG''
  set x'' : Fin 2 → α := ![x 0, x 2] with hx''
  set e'' : Fin 3 → β := ![e 0, e 1, e 3] with he''
  obtain ⟨hcover'', hinj'', hxV₁'', hpath'', hsep''⟩ :=
    splitOff_ear_three hcover hinj hxV₁ ha hb hab hpath hsep
  have he₁ : ∀ y y', G.IsLink (e 1) y y' → y ∉ V₁ ∨ y' ∉ V₁ := by
    intro y y' h
    rcases h.eq_and_eq_or_eq_and_eq l1 with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact Or.inl (hxV₁ 0)
    · exact Or.inl (hxV₁ 1)
  obtain ⟨hle₁'', hind⟩ := induce_splitOff_ear (x := x) (e₀ := e 1) (w := x 2) hcover hxV₁
    ⟨1, rfl⟩ (hxV₁ 0) he₁
  -- Steps 1–2: the main polynomial of `G`, the base data, and the selectors
  obtain ⟨Pm, hPm, hmain⟩ := G.exists_mvPolynomial_isMainPicture (K := K)
    hG.simple.toLoopless hG.three_le_ncard_closedNbhd
  set ends := G.endsOf with hendsdef
  have hends : ∀ f u w, G.IsLink f u w → G.IsLink f (ends f).1 (ends f).2 :=
    fun f _ _ hf => G.isLink_endsOf hf.edge_mem
  set ends'' := Function.update ends (e 1) (x 0, x 2) with hends''def
  have hends'' : ∀ f u w, G''.IsLink f u w → G''.IsLink f (ends'' f).1 (ends'' f).2 :=
    fun f _ _ hf => G.isLink_update_splitOff hends (hpath'' 1) f hf
  obtain ⟨q', z₁, la, lb, sstar, ρM, hqm', hadm₂, hpicstar, hrk₂, hne₂, hz₁s, hlas, hlbs, hρG,
      hρ2, hrk₁, hrk₁''⟩ :=
    Graph.exists_earBase_splitOff (xf := x 0) (xl := x 2) (X := Set.range x) (le_refl 2)
      hcover'' hinj'' hxV₁'' ha hb hab hpath'' hsep'' (hpath'' 1) he₁ hle₁'' hind hends
      (Or.inr ⟨e 0, hpath'' 0⟩) (Or.inr ⟨e 3, (hpath'' 2).symm⟩)
      (by rintro _ ⟨i, rfl⟩; fin_cases i <;> exact ⟨_, rfl⟩) h₁ h₂ hPm
  set cfg := earConfig V₁ q' z₁ (x 0) (x 2) (Set.range x) la lb with hcfgdef
  set P := earPointPoly (K := K) V₁ q' z₁ (x 0) (x 2) (Set.range x) la lb with hPdef
  have hPc : ∀ s, (fun p => MvPolynomial.eval s (P p)) = cfg s :=
    fun s => funext (eval_earPointPoly V₁ q' z₁ (x 0) (x 2) (Set.range x) la lb s)
  have hcV₁ : ∀ s w, w ∈ V₁ → ∀ j, cfg s (w, j) = pencilConfigPoint q' z₁ w j :=
    fun s w hw j => earConfig_of_mem s hw j
  set ρJ := ρM.map (screwComplementIso (K := K)).symm.toLinearMap with hρJ
  -- the points of the configurations, on the planes `la` and `lb` at the ends
  set pt : ((α × Fin 2) ⊕ α → K) → α → Fin 4 → K := fun s w j => cfg s (w, j) with hpt
  have hevpt : ∀ s w, (fun j => MvPolynomial.eval s (P (w, j))) = pt s w :=
    fun s w => funext fun j => congrFun (hPc s) (w, j)
  have hpt3 : ∀ s w, pt s w 3 = 1 := fun s w => rfl
  have hza : z₁ a = la ⬝ᵥ pencilPicturePoint q' a := by
    have := hlas sstar a (Or.inl rfl)
    rwa [hpicstar] at this
  have hzb : z₁ b = lb ⬝ᵥ pencilPicturePoint q' b := by
    have := hlbs sstar b (Or.inl rfl)
    rwa [hpicstar] at this
  have hpta : ∀ s, pt s a = liftPlane la (pencilPicturePoint q' a) := by
    intro s; funext j; simp only [hpt, hcV₁ s a ha]
    fin_cases j <;> simp [pencilConfigPoint, liftPlane, pencilPicturePoint, hza]
  have hptb : ∀ s, pt s b = liftPlane lb (pencilPicturePoint q' b) := by
    intro s; funext j; simp only [hpt, hcV₁ s b hb]
    fin_cases j <;> simp [pencilConfigPoint, liftPlane, pencilPicturePoint, hzb]
  have hpt0 : ∀ s, pt s (x 0) = liftPlane la ![s (Sum.inl (x 0, 0)), s (Sum.inl (x 0, 1)), 1] :=
    fun s => earConfig_first s (hxV₁ 0)
  have hpt2 : ∀ s, pt s (x 2) = liftPlane lb ![s (Sum.inl (x 2, 0)), s (Sum.inl (x 2, 1)), 1] :=
    fun s => earConfig_last s (hxV₁ 2) x02.symm
  -- the polynomial conditions on the ear data of `G″`
  set N'' := (screwDim 2 * ((V(G'').ncard : ℤ) - 1) - G''.deficiency 3).toNat with hN''def
  have hN'' : N'' ≤ Module.finrank K (Submodule.span K (PanelHingeFramework.ofNormals (k := 2)
      G'' ends'' (fun p => MvPolynomial.eval sstar (P p))).toBodyHinge.rigidityRows) := by
    rw [hPc]
    exact Int.toNat_le.mpr hrk₂.symm.le
  have hne'' : ∀ f, G''.IsLink f (ends'' f).1 (ends'' f).2 →
      (PanelHingeFramework.ofNormals (k := 2) G'' ends''
        (fun p => MvPolynomial.eval sstar (P p))).toBodyHinge.supportExtensor f ≠ 0 := by
    rw [hPc]
    exact hne₂
  obtain ⟨Q₂, hQ₂₀, hQ₂⟩ := exists_mvPolynomial_le_finrank_ofNormals_bind G'' ends'' hends'' P
    hne'' hN''
  obtain ⟨Pa, hPa₀, hPa⟩ := hadm₂.exists_mvPolynomial
  have hPa'₀ : MvPolynomial.eval sstar (MvPolynomial.bind₁ (earPicturePoly V₁ q') Pa) ≠ 0 := by
    rwa [eval_bind₁_earPicturePoly, hpicstar]
  have hne0 : ∀ {Q : MvPolynomial ((α × Fin 2) ⊕ α) K} {s}, MvPolynomial.eval s Q ≠ 0 → Q ≠ 0 :=
    fun h hQ => h (by rw [hQ, map_zero])
  -- Step 4: the case split on `ρ`, made before the ear data
  have hextra : ∃ Qx : MvPolynomial ((α × Fin 2) ⊕ α) K, Qx ≠ 0 ∧
      ∀ s, MvPolynomial.eval s Qx ≠ 0 → LinearIndependent K ![pt s (x 0), pt s (x 2)] →
        star (pt s (x 0)) ⊔ star (pt s (x 2)) ≤ ρJ ⊔ Submodule.span K
          {pointJoin (pt s a) (pt s (x 0)), pointJoin (pt s (x 0)) (pt s (x 2)),
            pointJoin (pt s (x 2)) (pt s b)} →
        ρJ ⊔ Submodule.span K {pointJoin (pt s a) (pt s (x 0)),
          pointJoin (pt s (x 0)) (pt s (x 2)), pointJoin (pt s (x 2)) (pt s b)} = ⊤ := by
    by_cases hB : ∀ c ∈ ρJ, ∀ u v, kleinLin (pointJoin (liftPlane la u) (liftPlane lb v)) c = 0
    · -- Case B: `dim W ≤ 3`, so `W` holds neither both stars
      refine ⟨1, one_ne_zero, fun s _ hli hle => absurd hle ?_⟩
      have hset : ({pointJoin (pt s a) (pt s (x 0)), pointJoin (pt s (x 0)) (pt s (x 2)),
          pointJoin (pt s (x 2)) (pt s b)} : Set (ScrewSpace K 2)) = Set.range
            ![pointJoin (pt s a) (pt s (x 0)), pointJoin (pt s (x 0)) (pt s (x 2)),
              pointJoin (pt s (x 2)) (pt s b)] := by
        simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
      rw [hset]
      refine not_star_sup_star_le_of_klein hB _ (fun hl i => ?_) hli
      fin_cases i
      · change pointJoin (pt s a) (pt s (x 0)) ∈ _
        rw [hpta, hpt0]; exact pointJoin_liftPlane_mem_planeLines _ _ _
      · change pointJoin (pt s (x 0)) (pt s (x 2)) ∈ _
        rw [hpt0, hpt2, ← hl]; exact pointJoin_liftPlane_mem_planeLines _ _ _
      · change pointJoin (pt s (x 2)) (pt s b) ∈ _
        rw [hpt2, hptb, ← hl]; exact pointJoin_liftPlane_mem_planeLines _ _ _
    · -- Case A: some `c ∈ ρ` pairs to a nonzero value with the join `y₁ ∧ y₃`
      push Not at hB
      obtain ⟨c, hc, u₀, v₀, hne⟩ := hB
      obtain ⟨u, v, hu, hv, hne'⟩ := exists_klein_liftPlane_affine_ne_zero hne
      set sw : (α × Fin 2) ⊕ α → K := Sum.elim
        (fun p => if p.1 = x 0 then ![u 0, u 1] p.2 else ![v 0, v 1] p.2) 0 with hsw
      have hw0 : pt sw (x 0) = liftPlane la u := by
        rw [hpt0]; congr 1; funext i; fin_cases i <;> simp [hsw, hu]
      have hw2 : pt sw (x 2) = liftPlane lb v := by
        rw [hpt2]; congr 1; funext i; fin_cases i <;> simp [hsw, x02.symm, hv]
      have hker : pointJoin (liftPlane la u) (liftPlane lb v) ∉ LinearMap.ker (kleinLin c) := by
        rw [LinearMap.mem_ker, ← kleinLin_comm]; exact hne'
      have hkert : LinearMap.ker (kleinLin c) ≠ ⊤ := fun h => hker (h ▸ Submodule.mem_top)
      have hjoin : ∀ s, (Set.range fun _ : Fin 1 =>
          pointJoin (fun j => MvPolynomial.eval s (P (x 0, j)))
            (fun j => MvPolynomial.eval s (P (x 2, j)))) =
          {pointJoin (pt s (x 0)) (pt s (x 2))} := by
        intro s; rw [hevpt, hevpt, Set.range_const]
      have h6 : 6 ≤ Module.finrank K ↥(LinearMap.ker (kleinLin c) ⊔ Submodule.span K
          (Set.range fun _ : Fin 1 => pointJoin (fun j => MvPolynomial.eval sw (P (x 0, j)))
            (fun j => MvPolynomial.eval sw (P (x 2, j))))) := by
        rw [hjoin, hw0, hw2, Submodule.finrank_sup_span_singleton hker]
        have := LinearMap.finrank_range_add_finrank_ker (kleinLin c)
        have h1 := Submodule.finrank_le (LinearMap.range (kleinLin c))
        rw [Module.finrank_self] at h1
        rw [finrank_screwSpace_two] at this
        omega
      obtain ⟨Qx, hQx₀, hQx⟩ := exists_mvPolynomial_le_finrank_sup_span_pointJoin
        (LinearMap.ker (kleinLin c)) P (fun _ : Fin 1 => x 0) (fun _ => x 2) h6
      refine ⟨Qx, hne0 hQx₀, fun s hs hli hle => ?_⟩
      have h6s := hQx s hs
      rw [hjoin] at h6s
      have hks : kleinLin c (pointJoin (pt s (x 0)) (pt s (x 2))) ≠ 0 := by
        intro h0
        rw [sup_eq_left.mpr ((Submodule.span_singleton_le_iff_mem _ _).mpr h0)] at h6s
        have hlt := Submodule.finrank_lt hkert
        rw [finrank_screwSpace_two] at hlt
        omega
      exact eq_top_of_star_sup_star_le hli (Submodule.mem_sup_left hc) hks hle
  obtain ⟨Qx, hQx₀, hQx⟩ := hextra
  -- Round 1: a common non-root `y` of the three
  obtain ⟨sy, hsy₂, hsya, hsyx⟩ := MvPolynomial.exists_eval_ne_zero₃ (hne0 hQ₂₀) (hne0 hPa'₀)
    hQx₀
  have hrank'' := hQ₂ sy hsy₂
  rw [hPc] at hrank''
  rw [eval_bind₁_earPicturePoly] at hsya
  have hadmy := hPa _ hsya
  have hli : LinearIndependent K ![pt sy (x 0), pt sy (x 2)] :=
    linearIndependent_pencilConfigPoint_pair _ (hadmy.1 _ _ _ (hpath'' 1))
  -- Step 2 at `G″`: `dim W ≥ 3 + f − def(G″)`
  have hC'' : ∀ i, (PanelHingeFramework.ofNormals (k := 2) G'' ends''
      (cfg sy)).toBodyHinge.supportExtensor (e'' i) ≠ 0 :=
    fun i => hadmy.supportExtensor_ne_zero hends'' _ (hpath'' i)
  have hear'' : (Module.finrank K ↥(Submodule.span K (PanelHingeFramework.ofNormals (k := 2) G''
      ends'' (cfg sy)).toBodyHinge.rigidityRows) : ℤ)
      = (Module.finrank K ↥(Submodule.span K (⟨G''.induce V₁, (PanelHingeFramework.ofNormals
            (k := 2) G'' ends'' (cfg sy)).toBodyHinge.supportExtensor⟩ :
              BodyHingeFramework K 2 α β).rigidityRows) : ℤ)
        + ((screwDim 2 : ℤ) - 1) * (2 + 1)
        + (Module.finrank K ↥((⟨G''.induce V₁, (PanelHingeFramework.ofNormals (k := 2) G'' ends''
              (cfg sy)).toBodyHinge.supportExtensor⟩ : BodyHingeFramework K 2 α β).relScrews a b
            ⊔ Submodule.span K (Set.range ((PanelHingeFramework.ofNormals (k := 2) G'' ends''
              (cfg sy)).toBodyHinge.supportExtensor ∘ e''))) : ℤ)
        - (screwDim 2 : ℤ) :=
    BodyHingeFramework.finrank_span_rigidityRows_ear_eq _ hinj'' hxV₁'' ha hb hab hpath'' hsep''
      hC''
  rw [hrk₁'' sy, hρ2 sy, span_supportExtensor_comp_eq_map_pointJoin hends'' (cfg sy) e''
    (fun i => pathVertex a x'' b i.castSucc) (fun i => pathVertex a x'' b i.succ) hpath'',
    finrank_sup_map_screwComplementIso] at hear''
  have hjoins'' : (fun i : Fin 3 => pointJoin (fun j => cfg sy (pathVertex a x'' b i.castSucc, j))
      (fun j => cfg sy (pathVertex a x'' b i.succ, j))) = ![pointJoin (pt sy a) (pt sy (x 0)),
        pointJoin (pt sy (x 0)) (pt sy (x 2)), pointJoin (pt sy (x 2)) (pt sy b)] := by
    funext i; fin_cases i <;> rfl
  have hset'' : Set.range ![pointJoin (pt sy a) (pt sy (x 0)),
        pointJoin (pt sy (x 0)) (pt sy (x 2)), pointJoin (pt sy (x 2)) (pt sy b)] =
      {pointJoin (pt sy a) (pt sy (x 0)), pointJoin (pt sy (x 0)) (pt sy (x 2)),
        pointJoin (pt sy (x 2)) (pt sy b)} := by
    simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rw [hjoins'', hset''] at hear''
  -- Step 3: `x 1` is put back next to `y₁` or `y₃`, or at `y₁` when `W = Λ²K⁴`
  obtain ⟨x₂, hx₂3, hins⟩ := exists_insertion_three ρJ (pt sy a) (pt sy (x 0)) (pt sy (x 2))
    (pt sy b) (hpt3 _ _) (hpt3 _ _) (hQx sy hsyx hli)
  -- the counts
  set f₁ := (G.induce V₁).deficiency 3 with hf₁
  set dG := G.deficiency 3 with hdG
  set d'' := G''.deficiency 3 with hd''
  have hdisj : Disjoint V₁ (Set.range x) := by
    refine Set.disjoint_left.mpr ?_
    rintro _ h ⟨i, rfl⟩
    exact hxV₁ i h
  have hcount : (V(G).ncard : ℤ) = V₁.ncard + 3 := by
    rw [hcover, Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _),
      Set.ncard_range_of_injective hinj, Nat.card_eq_fintype_card, Fintype.card_fin]
    push_cast; ring
  have hcount'' : (V(G'').ncard : ℤ) = V₁.ncard + 2 := by
    have hdisj'' : Disjoint V₁ (Set.range x'') := by
      refine Set.disjoint_left.mpr ?_
      rintro _ h ⟨i, rfl⟩
      exact hxV₁'' i h
    rw [hcover'', Set.ncard_union_eq hdisj'' (Set.toFinite _) (Set.toFinite _),
      Set.ncard_range_of_injective hinj'', Nat.card_eq_fintype_card, Fintype.card_fin]
    push_cast; ring
  have hdeg2 : ∀ e' y, G.IsLink e' (x 1) y → e' = e 1 ∨ e' = e 2 := by
    intro e' y hl
    by_cases h : ∃ i, e' = e i
    · obtain ⟨i, rfl⟩ := h
      fin_cases i
      · rcases hl.eq_and_eq_or_eq_and_eq l0 with ⟨h1, -⟩ | ⟨h1, -⟩
        exacts [absurd h1 (hax 1), absurd h1 x01.symm]
      · exact Or.inl rfl
      · exact Or.inr rfl
      · rcases hl.eq_and_eq_or_eq_and_eq l3 with ⟨h1, -⟩ | ⟨h1, -⟩
        exacts [absurd h1 x12, absurd h1 (hbx 1)]
    · exact absurd (hsep e' _ _ hl (fun i h' => h ⟨i, h'⟩)).1 (hxV₁ 1)
  have hdef'' : d'' ≤ dG := Graph.splitOff_deficiency_le_of_eq_left (n := 3) (by decide)
    x01 x12.symm (fun h => by simpa using pathEdge_injective hinj hax hbx hab hpath h) l1.symm l2
    hdeg2
  have hdefG : f₁ + 3 + 1 - (Graph.bodyBarDim 3 : ℤ) ≤ dG :=
    Graph.deficiency_induce_add_le_of_ear (n := 3) (k := 3) (by decide) (by omega) hcover hinj hxV₁
      ha hb hpath hsep
  have hs6 : (screwDim 2 : ℤ) = 6 := rfl
  have hb6 : (Graph.bodyBarDim 3 : ℤ) = 6 := rfl
  -- `dim W ≥ 3 + f − def(G″)`
  have hW : 3 + f₁ - d'' ≤ (Module.finrank K ↥(ρJ ⊔ Submodule.span K
      {pointJoin (pt sy a) (pt sy (x 0)), pointJoin (pt sy (x 0)) (pt sy (x 2)),
        pointJoin (pt sy (x 2)) (pt sy b)}) : ℤ) := by
    have h1 : screwDim 2 * ((V(G'').ncard : ℤ) - 1) - d'' ≤
        (Module.finrank K ↥(Submodule.span K (PanelHingeFramework.ofNormals (k := 2) G'' ends''
          (cfg sy)).toBodyHinge.rigidityRows) : ℤ) :=
      (Int.self_le_toNat _).trans (by exact_mod_cast hrank'')
    rw [hear'', hcount''] at h1
    rw [hs6] at h1
    linarith
  -- put `x 1` back at `x₂`
  set st := Function.update (Function.update (Function.update sy (Sum.inl (x 1, 0)) (x₂ 0))
    (Sum.inl (x 1, 1)) (x₂ 1)) (Sum.inr (x 1)) (x₂ 2) with hst
  have hpt1 : pt st (x 1) = x₂ := by
    change (fun j => cfg st (x 1, j)) = x₂
    rw [earConfig_of_mem_X st (hxV₁ 1) x01.symm x12 (Set.mem_range_self 1)]
    funext j; fin_cases j <;> simp [hst, hx₂3]
  have hptne : ∀ w, w ≠ x 1 → pt st w = pt sy w := by
    intro w hw
    funext j
    exact earConfig_congr (fun i => by simp [hst, hw]) (by simp [hst, hw]) j
  have hjoinsG : (fun i : Fin 4 => pointJoin (pt st (pathVertex a x b i.castSucc))
      (pt st (pathVertex a x b i.succ))) = ![pointJoin (pt sy a) (pt sy (x 0)),
        pointJoin (pt sy (x 0)) x₂, pointJoin x₂ (pt sy (x 2)),
        pointJoin (pt sy (x 2)) (pt sy b)] := by
    have ha1 : a ≠ x 1 := (hax 1).symm
    have hb1 : b ≠ x 1 := (hbx 1).symm
    funext i
    fin_cases i
    · change pointJoin (pt st a) (pt st (x 0)) = _
      rw [hptne _ ha1, hptne _ x01]; rfl
    · change pointJoin (pt st (x 0)) (pt st (x 1)) = _
      rw [hptne _ x01, hpt1]; rfl
    · change pointJoin (pt st (x 1)) (pt st (x 2)) = _
      rw [hpt1, hptne _ x12.symm]; rfl
    · change pointJoin (pt st (x 2)) (pt st b) = _
      rw [hptne _ x12.symm, hptne _ hb1]; rfl
  have hsetG : Set.range ![pointJoin (pt sy a) (pt sy (x 0)),
        pointJoin (pt sy (x 0)) x₂, pointJoin x₂ (pt sy (x 2)),
        pointJoin (pt sy (x 2)) (pt sy b)] =
      {pointJoin (pt sy a) (pt sy (x 0)), pointJoin (pt sy (x 0)) x₂, pointJoin x₂ (pt sy (x 2)),
        pointJoin (pt sy (x 2)) (pt sy b)} := by
    simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  -- the target `n₀ = 4 + f − def(G)` is met at `st`
  set n₀ := (4 + f₁ - dG).toNat with hn₀
  have hNt : n₀ ≤ Module.finrank K ↥(ρJ ⊔ Submodule.span K (Set.range fun i : Fin 4 =>
      pointJoin (fun j => MvPolynomial.eval st (P (pathVertex a x b i.castSucc, j)))
        (fun j => MvPolynomial.eval st (P (pathVertex a x b i.succ, j))))) := by
    rw [show (fun i : Fin 4 =>
        pointJoin (fun j => MvPolynomial.eval st (P (pathVertex a x b i.castSucc, j)))
          (fun j => MvPolynomial.eval st (P (pathVertex a x b i.succ, j)))) =
        fun i => pointJoin (pt st (pathVertex a x b i.castSucc)) (pt st (pathVertex a x b i.succ))
      from funext fun i => by rw [hevpt, hevpt]]
    rw [hjoinsG, hsetG]
    refine le_trans ?_ hins
    rw [le_min_iff]
    constructor
    · refine Int.toNat_le.mpr ?_
      push_cast
      linarith
    · refine Int.toNat_le.mpr ?_
      push_cast
      rw [hb6] at hdefG
      linarith
  obtain ⟨Qs, hQs₀, hQs⟩ := exists_mvPolynomial_le_finrank_sup_span_pointJoin ρJ P
    (fun i : Fin 4 => pathVertex a x b i.castSucc) (fun i => pathVertex a x b i.succ) hNt
  have hPm'₀ : MvPolynomial.eval sstar (MvPolynomial.bind₁ (earPicturePoly V₁ q') Pm) ≠ 0 := by
    rwa [eval_bind₁_earPicturePoly, hpicstar]
  -- Round 2: a common non-root, main for `G`
  obtain ⟨s₀, hs₀a, hs₀b⟩ := MvPolynomial.exists_eval_ne_zero₂ (hne0 hQs₀) (hne0 hPm'₀)
  rw [eval_bind₁_earPicturePoly] at hs₀b
  have hqmain₀ := hmain _ hs₀b
  have hz₀ := Graph.earHeight_mem_liftingSpace (k := 3) (by norm_num) hcover hinj hxV₁ ha hb hab
    hpath hsep hqmain₀.1 (hz₁s s₀) (hlas s₀) (hlbs s₀) (fun w => s₀ (Sum.inr w))
  -- the ear rank law at `G`
  have hC : ∀ i, (PanelHingeFramework.ofNormals (k := 2) G ends
      (cfg s₀)).toBodyHinge.supportExtensor (e i) ≠ 0 :=
    fun i => hqmain₀.1.supportExtensor_ne_zero hends _ (hpath i)
  have hear : (Module.finrank K ↥(Submodule.span K (PanelHingeFramework.ofNormals (k := 2) G ends
      (cfg s₀)).toBodyHinge.rigidityRows) : ℤ)
      = (Module.finrank K ↥(Submodule.span K (⟨G.induce V₁, (PanelHingeFramework.ofNormals
            (k := 2) G ends (cfg s₀)).toBodyHinge.supportExtensor⟩ :
              BodyHingeFramework K 2 α β).rigidityRows) : ℤ)
        + ((screwDim 2 : ℤ) - 1) * (3 + 1)
        + (Module.finrank K ↥((⟨G.induce V₁, (PanelHingeFramework.ofNormals (k := 2) G ends
              (cfg s₀)).toBodyHinge.supportExtensor⟩ : BodyHingeFramework K 2 α β).relScrews a b
            ⊔ Submodule.span K (Set.range ((PanelHingeFramework.ofNormals (k := 2) G ends
              (cfg s₀)).toBodyHinge.supportExtensor ∘ e))) : ℤ)
        - (screwDim 2 : ℤ) :=
    BodyHingeFramework.finrank_span_rigidityRows_ear_eq _ hinj hxV₁ ha hb hab hpath hsep hC
  rw [hrk₁ s₀, hρG s₀, span_supportExtensor_comp_eq_map_pointJoin hends (cfg s₀) e
    (fun i => pathVertex a x b i.castSucc) (fun i => pathVertex a x b i.succ) hpath,
    finrank_sup_map_screwComplementIso] at hear
  have hspan₀ := hQs s₀ hs₀a
  rw [show (fun i : Fin 4 =>
      pointJoin (fun j => MvPolynomial.eval s₀ (P (pathVertex a x b i.castSucc, j)))
        (fun j => MvPolynomial.eval s₀ (P (pathVertex a x b i.succ, j)))) =
      fun i => pointJoin (pt s₀ (pathVertex a x b i.castSucc)) (pt s₀ (pathVertex a x b i.succ))
    from funext fun i => by rw [hevpt, hevpt]] at hspan₀
  refine Graph.x0Attains_of_exists hV ends hends hqmain₀ hz₀ ?_
  change _ ≤ (Module.finrank K ↥(Submodule.span K (PanelHingeFramework.ofNormals (k := 2) G ends
    (cfg s₀)).toBodyHinge.rigidityRows) : ℤ)
  rw [hear, hcount, hs6]
  have h₀ : ((4 + f₁ - dG : ℤ)) ≤ (n₀ : ℤ) := Int.self_le_toNat _
  have h₁ : (n₀ : ℤ) ≤ (Module.finrank K ↥(ρJ ⊔ Submodule.span K (Set.range fun i : Fin 4 =>
      pointJoin (pt s₀ (pathVertex a x b i.castSucc)) (pt s₀ (pathVertex a x b i.succ)))) : ℤ) := by
    exact_mod_cast hspan₀
  change _ ≤ _ + _ + (Module.finrank K ↥(ρJ ⊔ Submodule.span K (Set.range fun i : Fin 4 =>
      pointJoin (pt s₀ (pathVertex a x b i.castSucc)) (pt s₀ (pathVertex a x b i.succ)))) : ℤ) - _
  linarith

end CombinatorialRigidity.Molecular
