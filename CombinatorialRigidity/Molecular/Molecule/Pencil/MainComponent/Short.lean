/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.Molecule.Pencil.MainComponent.EarGen

/-!
# Open ears with two, three or four interior bodies

The steps of the induction on the general configuration at an open ear `a − x 0 − ⋯ − x (k − 1) − b`
on `V₁` with two, three or four interior bodies, whose ends may be adjacent
(`thm:pencil-x0-open-ear-two`, `thm:pencil-x0-open-ear-three`, `thm:pencil-x0-open-ear-four`,
`sec:main-component-short`). An ear is given as in `MainComponent/Ear.lean`. The steps follow the
scheme of `sec:main-component-cut` (`MainComponent/Cut.lean`), with the ear rank formula
(`BodyHingeFramework.finrank_span_rigidityRows_ear_eq`, `lem:block-rank-ear`) for the count: a
configuration over a main picture of `G`, at which `G[V₁]` has its target, has rank at least the
target of `G` once `dim(ρ + Λ) ≥ k + 1 + def₃(G[V₁]) − def₃(G)`, the inequality `(⋆)` of the
section, where `ρ` is the space of relative screws of `a` and `b` in `G[V₁]` and `Λ` the span of the
joins of the ear.

With two interior bodies, given `def₃(G[V₁]) ≤ def₃(G)`, three independent joins of the ear give
`(⋆)`. They are independent at one flat configuration, three joins of the closed hexagon of
`lem:pencil-chain-span-certificates`, whose picture need not be admissible, and the heights `0` lie
in every `L_G(q)`: `Graph.X0Attains.of_openEar_of_cert` (`MainComponent/Ear.lean`) does the rest, as
at five or more interior bodies.

With three or four interior bodies no bound on the deficiencies is assumed. The step also uses
`G″ = G.splitOff (x 1) (x 0) (x 2) (e 1)`, `G` with its second interior body suppressed and the
label `e 1` of `x 0 − x 1` relinked to `x 0 − x 2`. It has the same `G[V₁]`, an open ear on `V₁`
with one interior body fewer, and a deficiency at most that of `G`
(`Graph.splitOff_deficiency_le_of_eq_left`, `lem:splitoff-deficiency-reuse`). The count is against
`G″`. With `W` the span of `ρ` and the joins of the ear of `G″`, the ear rank formula at `G″` bounds
`dim W` below where `G[V₁]` and `G″` have their targets, and `(⋆)` then asks for no more than
`min(dim W + 1, 6)` (`Graph.deficiency_induce_add_le_of_ear`, `lem:deficiency-ear`). Putting `x 1`
back on a line through the point of `x 0` or of `x 2` gains the dimension, unless `W` already
contains the star of that point, every line through it (`lem:pencil-insertion`,
`lem:pencil-two-stars`). So it suffices that a `W` containing both stars be the whole screw space
`Λ²K⁴`, and then `x 1` goes to the point of `x 0` (`exists_insertion_four`,
`exists_insertion_three`, `MainComponent/Lines.lean`).

At four interior bodies a `W` containing both stars contains the six joins of the points of `x 0`,
`x 2`, `x 3` and `b`, which span `Λ²K⁴` when the four points are independent
(`lem:pencil-tetrahedron`, the case `d = 3` of KT 2011 Lemma 2.1, pp. 651–652); the ear data are
asked for the span, which holds at one ear datum (`linearIndependent_tetra_witness`). At three
interior bodies the case split on `ρ` comes before the ear data. Either every relative screw pairs
to zero with every line joining the planes of `a` and of `b`, and then `W` has dimension at most
three and cannot contain both stars, which span at least five dimensions (`lem:pencil-bilinear`,
`lem:pencil-two-stars`); or some `c ∈ ρ` does not, and the ear data are also asked for
`⟨c, y₁ ∧ y₃⟩ ≠ 0`, `y₁` and `y₃` the points of `x 0` and `x 2`, written as the span bound
`dim(ker⟨c, ·⟩ + K (y₁ ∧ y₃)) ≥ 6` and met at a pair of affine points
(`exists_klein_liftPlane_affine_ne_zero`). Then a `W` containing both stars contains `c`, which lies
outside them, and is `Λ²K⁴`.

The configuration is chosen in two stages, the base data and then the ear data
(`def:pencil-ear-data`, `MainComponent/EarGen.lean`). The base data are fixed first
(`Graph.exists_earBase_splitOff`): a picture off the polynomials of the attainment at `G[V₁]` and at
`G″` and off the main-picture polynomial of `G`, and a height of `G″` at which both have their
targets, whose restriction to `V₁` fixes `ρ` and the rank of `G[V₁]` at every ear datum. One space
of ear data serves `G` and `G″`, and each condition the step asks of them holds off the zero set of
a polynomial that is nonzero at one ear datum (`lem:pencil-ear-data-picture`,
`lem:pencil-ear-data-open`). The ear data are taken twice (`Graph.X0Attains.of_openEar_splitOff`):
for `G″`, where it has at least its target rank and an admissible picture and `x 1` can be put back;
then, with `x 1` put back, for `G`, off the zero sets of the span bound so reached and of the
main-picture polynomial of `G`. The span bound asks no nonzero hinge of the ear datum where it
holds, unlike the rank bound (`exists_mvPolynomial_le_finrank_sup_span_pointJoin`,
`exists_mvPolynomial_le_finrank_ofNormals_bind`): the point where `x 1` is put back certifies
`dim(ρ + Λ)`, not the rank of `G`, and may be the point of `x 0`, with a zero join.

## Main results

* `Graph.X0Attains.of_openEar_two`: `thm:pencil-x0-open-ear-two`, if `G` satisfies the standing
  hypotheses, with an open ear on `V₁` with two interior bodies, its ends possibly adjacent, and
  `def₃(G[V₁]) ≤ def₃(G)`, the general configuration of `G` attains when that of `G[V₁]` does.
* `Graph.X0Attains.of_openEar_four` and `Graph.X0Attains.of_openEar_three`:
  `thm:pencil-x0-open-ear-four` and `thm:pencil-x0-open-ear-three`, the same at four and at three
  interior bodies, with no bound on the deficiencies, when the general configurations of `G[V₁]` and
  of `G″` attain.
* `splitOff_ear_four` and `splitOff_ear_three`: steps of the two, `G″` has the open ear
  `a − x 0 − x 2 − x 3 − b`, resp. `a − x 0 − x 2 − b`, on `V₁`; `induce_splitOff_ear`, with the
  same `G[V₁]`. A selector of `G`, relinked at the freed label, records the links of the split-off
  (`PanelHingeFramework.RecordsLinks.update_splitOff`).
* `Graph.exists_earBase_splitOff` and `Graph.X0Attains.of_openEar_splitOff`: steps of the two, the
  base data, and the two choices of ear data and the count, given that `x 1` can be put back off a
  polynomial in the ear data.
* `linearIndependent_tetra_witness`: a step of `thm:pencil-x0-open-ear-four`, the four independent
  points at the ear datum where the six joins of the points of `x 0`, `x 2`, `x 3` and `b` span
  `Λ²K⁴`.
-/

open scoped Graph

namespace CombinatorialRigidity.Molecular

variable {K : Type*} [Field K] {α β : Type*}

/-! ## The open ear with two interior bodies (`thm:pencil-x0-open-ear-two`) -/

/-- **An open ear with two interior bodies** (`thm:pencil-x0-open-ear-two`). Let `G` satisfy the
standing hypotheses, with an open ear `a − x 0 − x 1 − b` on `V₁` whose ends may be adjacent, and
let `def₃(G[V₁]) ≤ def₃(G)`; `Graph.deficiency_induce_le_of_ear_of_merge`
(`lem:deficiency-ear-merge`) gives it when some partition of `V₁` attaining `def₃(G[V₁])` puts `a`
and `b` in one part. If the general configuration of `G[V₁]` attains, so does that of `G`.

Proof. `Graph.X0Attains.of_openEar_of_cert`, with the three joins of the ear. The heights `0` lie in
every `L_G(q)`, and at them the joins are independent at one picture (`certPicture`), which puts the
points of `a`, `x 0`, `x 1` and `b` at `Y₄`, `Y₅`, `Y₀` and `Y₁`, and every other body's at `Y₄`:
three joins of the closed hexagon (`linearIndependent_pointJoin_certHexagon`). Independence is open
in the picture, then in the heights, and the ear rank formula adds at least `5 · 3 + 3 − 6 = 12` to
the rank, no less than the growth `12 − def₃(G) + def₃(G[V₁])` of the target. -/
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
  have hax : ∀ i, x i ≠ a := fun i h => hxV₁ i (h ▸ ha)
  have hbx : ∀ i, x i ≠ b := fun i h => hxV₁ i (h ▸ hb)
  have x01 : x 0 ≠ x 1 := fun h => absurd (hinj h) (by decide)
  -- the three ear links `a x 0, x 0 x 1, x 1 b`
  set u3 : Fin 3 → α := ![a, x 0, x 1]
  set v3 : Fin 3 → α := ![x 0, x 1, b]
  have hl3 : ∀ i, G.IsLink (e (id i)) (u3 i) (v3 i) := by
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
  refine Graph.X0Attains.of_openEar_of_cert hG le_rfl hcover hinj hxV₁ ha hb hab hpath hsep h₁
    u3 v3 id hl3 q₀ 0 hcert (fun _ _ => Submodule.zero_mem _) ?_
  push_cast
  linarith

/-! ## Suppressing the second interior body -/

section Antecedent

/-- **Suppressing the second interior body of a four-body ear** (a step of
`thm:pencil-x0-open-ear-four`): suppressing `x 1` and relinking `e 1` to `x 0 − x 2` leaves the ear
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

/-- **Suppressing the second interior body of a three-body ear** (a step of
`thm:pencil-x0-open-ear-three`): suppressing `x 1` and relinking `e 1` to `x 0 − x 2` leaves the ear
`a − x 0 − x 2 − b` on `V₁`, with the labels `e 0, e 1, e 3`. -/
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

/-- **Splitting off an interior body keeps `G[V₁]`** (a step of `thm:pencil-x0-open-ear-four`,
`thm:pencil-x0-open-ear-three` and `thm:pencil-x0-open-ear-two-orbit`): if `v` is an interior body
of the ear, `u ∉ V₁`, and `e₀` links no two bodies of `V₁` in `G`, then `G[V₁]` is a subgraph of
`G.splitOff v u w e₀`, and is its subgraph induced on `V₁`. -/
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

end Antecedent

/-! ## Four independent points (`thm:pencil-x0-open-ear-four`) -/

/-- **Four independent points** (a step of `thm:pencil-x0-open-ear-four`, the ear datum at which the
six joins span `Λ²K⁴`): the points over the pictures `(b₀, b₁ + 1)`, `(b₀, b₁)` and `(b₀ + 1, b₁)`
at the heights `γ`, `b₂ + 1` and `δ`, and `(b₀, b₁, b₂, 1)`, are linearly independent for every `γ`
and `δ`. In the step they are the points of `x 0`, `x 2`, `x 3` and `b`, with `(b₀, b₁)` the picture
of `b` and `b₂` its height. -/
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

/-! ## The base data of the steps at three and four interior bodies (`def:pencil-ear-data`) -/

open Classical in
/-- **The base data of the steps at three and four interior bodies** (a step of
`thm:pencil-x0-open-ear-four` and `thm:pencil-x0-open-ear-three`, their first stage). Let
`H = G.splitOff v u w e₀` have an open ear `a − y − b` on `V₁` with at least two interior bodies,
with the same subgraph on `V₁` as `G`, and let the ear data read the planes at `xf ∈ N_H[a]` and
`xl ∈ N_H[b]`. If `G[V₁]` and `H` attain, there are base data `(q, z₁, la, lb)` with:
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
  have hle : G.induce V₁ ≤ H := hind ▸ Graph.induce_le (hcover ▸ Set.subset_union_left)
  set ends'' := Function.update ends e₀ (u, w) with hends''def
  have hendsG := PanelHingeFramework.recordsLinks_iff_forall_isLink.mpr hends
  have hends'' : ∀ f p p', H.IsLink f p p' → H.IsLink f (ends'' f).1 (ends'' f).2 :=
    fun _ _ _ => (hendsG.update_splitOff hl₀).isLink
  have hendsI := PanelHingeFramework.recordsLinks_iff_forall_isLink.mp (hendsG.induce V₁)
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

/-! ## Three and four interior bodies, given that the suppressed body can be put back -/

open Classical in
/-- **The steps at three and four interior bodies, given that `v` can be put back** (a step of
`thm:pencil-x0-open-ear-four` and `thm:pencil-x0-open-ear-three`). Let `G` satisfy the standing
hypotheses, with an open ear `a − x 0 − ⋯ − x m − b` on `V₁`, `m ≥ 2`, and let
`G″ = G.splitOff v u w e₀`, `G` with the interior body `v` suppressed and `e₀` relinked from `u − v`
to `u − w`, have the open ear `a − y − b` on `V₁`, with `def₃(G″) ≤ def₃(G)`. Suppose that `v` can
be put back off a polynomial: over any base data `(q, z, la, lb)`, `z` on the plane `la` at `a` and
on `lb` at `b`, and any subspace `ρ`, some nonzero polynomial in the ear data `s` has, at every `s`
off it at which the picture is admissible for `G″`, an affine `x₂` such that every point assignment
that agrees with the configuration of `s` off `v` and puts `x₂` at `v` gives
`dim(ρ + Λ_G) ≥ min(dim(ρ + Λ_{G″}) + 1, 6)`, where `Λ_G` and `Λ_{G″}` are the spans of the joins of
the ears of `G` and `G″`. If the general configurations of `G[V₁]` and of `G″` attain, so does that
of `G`.

Proof. The base data are `Graph.exists_earBase_splitOff`'s, at the main-picture polynomial of `G`,
with `ρ` the relative screws of `a` and `b` in `G[V₁]`. Ear data off three polynomials give `G″` at
least its target rank and an admissible picture, and let `v` be put back; the ear rank formula at
`G″` bounds `dim(ρ + Λ_{G″})`, and with `v` put back the ear data of `G` meet `(⋆)`
(`Graph.deficiency_induce_add_le_of_ear` for the bound `6`). Ear data of `G` off the polynomial of
that span bound and off the main-picture polynomial of `G` then give `G` its target. The four-body
step puts `v` back by the tetrahedron (`exists_insertion_four`), the three-body step by the case
split on `ρ` (`exists_insertion_three`). -/
theorem _root_.Graph.X0Attains.of_openEar_splitOff [Infinite K] [Finite α] [Finite β]
    {G : Graph α β} (hG : G.IsX0Graph) {V₁ : Set α} {m : ℕ} (hm : 2 ≤ m)
    {x : Fin (m + 1) → α} {a b : α} {e : Fin (m + 2) → β} (hcover : V(G) = V₁ ∪ Set.range x)
    (hinj : Function.Injective x) (hxV₁ : ∀ i, x i ∉ V₁) (ha : a ∈ V₁) (hb : b ∈ V₁)
    (hab : a ≠ b)
    (hpath : ∀ i : Fin (m + 2),
      G.IsLink (e i) (pathVertex a x b i.castSucc) (pathVertex a x b i.succ))
    (hsep : ∀ f u w, G.IsLink f u w → (∀ i, f ≠ e i) → u ∈ V₁ ∧ w ∈ V₁)
    {v u w : α} {e₀ : β} {y : Fin m → α} {e'' : Fin (m + 1) → β}
    (hcover'' : V(G.splitOff v u w e₀) = V₁ ∪ Set.range y) (hinj'' : Function.Injective y)
    (hyV₁ : ∀ i, y i ∉ V₁)
    (hpath'' : ∀ i : Fin (m + 1), (G.splitOff v u w e₀).IsLink (e'' i)
      (pathVertex a y b i.castSucc) (pathVertex a y b i.succ))
    (hsep'' : ∀ f p p', (G.splitOff v u w e₀).IsLink f p p' → (∀ i, f ≠ e'' i) →
      p ∈ V₁ ∧ p' ∈ V₁)
    (hyx : Set.range y ⊆ Set.range x) (hv : v ∈ Set.range x) (hu : u ∉ V₁)
    (hl₀ : G.IsLink e₀ u v) (hl₀'' : (G.splitOff v u w e₀).IsLink e₀ u w)
    (hdef : (G.splitOff v u w e₀).deficiency 3 ≤ G.deficiency 3) {xf xl : α}
    (hxf : x ⟨0, by omega⟩ = xf) (hxl : x ⟨m, by omega⟩ = xl) (hvf : v ≠ xf) (hvl : v ≠ xl)
    (hins : ∀ (q : α × Fin 2 → K) (z : α → K) (la lb : Fin 3 → K)
      (ρ : Submodule K (ScrewSpace K 2)), z a = la ⬝ᵥ pencilPicturePoint q a →
      z b = lb ⬝ᵥ pencilPicturePoint q b →
      ∃ Q : MvPolynomial ((α × Fin 2) ⊕ α) K, Q ≠ 0 ∧ ∀ s, MvPolynomial.eval s Q ≠ 0 →
        (G.splitOff v u w e₀).IsAdmissiblePicture (earPicture V₁ q s) →
        ∃ x₂ : Fin 4 → K, x₂ 3 = 1 ∧ ∀ p : α → Fin 4 → K, p v = x₂ →
          (∀ t, t ≠ v → p t = fun j => earConfig V₁ q z xf xl (Set.range x) la lb s (t, j)) →
          min (Module.finrank K ↥(ρ ⊔ Submodule.span K (Set.range fun i : Fin (m + 1) =>
            pointJoin (fun j => earConfig V₁ q z xf xl (Set.range x) la lb s
                (pathVertex a y b i.castSucc, j))
              (fun j => earConfig V₁ q z xf xl (Set.range x) la lb s
                (pathVertex a y b i.succ, j)))) + 1) 6 ≤
          Module.finrank K ↥(ρ ⊔ Submodule.span K (Set.range fun i : Fin (m + 2) =>
            pointJoin (p (pathVertex a x b i.castSucc)) (p (pathVertex a x b i.succ)))))
    (h₁ : (G.induce V₁).X0Attains K) (h₂ : (G.splitOff v u w e₀).X0Attains K) :
    G.X0Attains K := by
  have hV : V(G).Nonempty := hG.connected.nonempty
  have : Inhabited α := ⟨a⟩
  have hvV₁ : v ∉ V₁ := by obtain ⟨i, rfl⟩ := hv; exact hxV₁ i
  set G'' := G.splitOff v u w e₀
  have he₀ : ∀ p p', G.IsLink e₀ p p' → p ∉ V₁ ∨ p' ∉ V₁ := fun p p' h => by
    rcases h.eq_and_eq_or_eq_and_eq hl₀ with ⟨-, rfl⟩ | ⟨rfl, -⟩
    exacts [Or.inr hvV₁, Or.inl hvV₁]
  obtain ⟨-, hind⟩ := induce_splitOff_ear hcover hxV₁ hv hu he₀
  -- the first and the last edge of the ear avoid `v`, so they stay links of `G″`
  have hkeep : ∀ f p y, G.IsLink f p y → p ∈ V₁ → v ≠ y → y ∈ G''.closedNbhd p := by
    intro f p y hf hp hvy
    refine Or.inr ⟨f, Or.inl ⟨fun h => ?_, hf, fun h => hvV₁ (h ▸ hp), fun h => hvy h.symm⟩⟩
    rw [h] at hf
    rcases hf.eq_and_eq_or_eq_and_eq hl₀ with ⟨-, h'⟩ | ⟨h', -⟩
    exacts [hvy h'.symm, hvV₁ (h' ▸ hp)]
  -- the main polynomial of `G`, the selectors, and the base data
  obtain ⟨Pm, hPm, hmain⟩ := G.exists_mvPolynomial_isMainPicture (K := K)
    hG.simple.toLoopless hG.three_le_ncard_closedNbhd
  set ends := G.endsOf
  have hends : ∀ f p p', G.IsLink f p p' → G.IsLink f (ends f).1 (ends f).2 :=
    fun f _ _ hf => G.isLink_endsOf hf.edge_mem
  set ends'' := Function.update ends e₀ (u, w)
  have hends'' : ∀ f p p', G''.IsLink f p p' → G''.IsLink f (ends'' f).1 (ends'' f).2 :=
    fun _ _ _ =>
      ((PanelHingeFramework.recordsLinks_iff_forall_isLink.mpr hends).update_splitOff hl₀'').isLink
  obtain ⟨q', z₁, la, lb, sstar, ρM, hqm', hadm₂, hpicstar, hrk₂, hne₂, hz₁s, hlas, hlbs, hρG,
      hρ2, hrk₁, hrk₁''⟩ :=
    Graph.exists_earBase_splitOff hm hcover'' hinj'' hyV₁ ha hb hab hpath'' hsep'' hl₀'' he₀ hind
      hends (hkeep _ _ _ (hxf ▸ ear_isLink_first hpath (by omega)) ha hvf)
      (hkeep _ _ _ (hxl ▸ (ear_isLink_last hpath (by omega)).symm) hb hvl) hyx h₁ h₂ hPm
  set ρJ := ρM.map (screwComplementIso (K := K)).symm.toLinearMap with hρJ
  -- the insertion hypothesis, a polynomial condition on the ear data
  obtain ⟨Qx, hQx₀, hQx⟩ := hins q' z₁ la lb ρJ
    (by have := hlas sstar a (Or.inl rfl); rwa [hpicstar] at this)
    (by have := hlbs sstar b (Or.inl rfl); rwa [hpicstar] at this)
  set cfg := earConfig V₁ q' z₁ xf xl (Set.range x) la lb
  set P := earPointPoly (K := K) V₁ q' z₁ xf xl (Set.range x) la lb
  have hPc : ∀ s p, MvPolynomial.eval s (P p) = cfg s p :=
    eval_earPointPoly V₁ q' z₁ xf xl (Set.range x) la lb
  have hPc' : ∀ s, (fun p => MvPolynomial.eval s (P p)) = cfg s := fun s => funext (hPc s)
  have hfam : ∀ s {ι : Type} (u' w' : ι → α),
      (fun i => pointJoin (fun j => MvPolynomial.eval s (P (u' i, j)))
        (fun j => MvPolynomial.eval s (P (w' i, j)))) =
      fun i => pointJoin (fun j => cfg s (u' i, j)) (fun j => cfg s (w' i, j)) :=
    fun s _ u' w' => funext fun i => by simp only [hPc]
  -- the rank and admissibility conditions on the ear data of `G″`
  set N'' := (screwDim 2 * ((V(G'').ncard : ℤ) - 1) - G''.deficiency 3).toNat
  have hN'' : N'' ≤ Module.finrank K (Submodule.span K (PanelHingeFramework.ofNormals (k := 2)
      G'' ends'' (fun p => MvPolynomial.eval sstar (P p))).toBodyHinge.rigidityRows) := by
    rw [hPc']
    exact Int.toNat_le.mpr hrk₂.symm.le
  have hne'' : ∀ f, G''.IsLink f (ends'' f).1 (ends'' f).2 →
      (PanelHingeFramework.ofNormals (k := 2) G'' ends''
        (fun p => MvPolynomial.eval sstar (P p))).toBodyHinge.supportExtensor f ≠ 0 := by
    rw [hPc']
    exact hne₂
  obtain ⟨Q₂, hQ₂₀, hQ₂⟩ := exists_mvPolynomial_le_finrank_ofNormals_bind G'' ends'' hends'' P
    hne'' hN''
  obtain ⟨Pa, hPa₀, hPa⟩ := hadm₂.exists_mvPolynomial
  have hPa'₀ : MvPolynomial.eval sstar (MvPolynomial.bind₁ (earPicturePoly V₁ q') Pa) ≠ 0 := by
    rwa [eval_bind₁_earPicturePoly, hpicstar]
  have hne0 : ∀ {Q : MvPolynomial ((α × Fin 2) ⊕ α) K} {s}, MvPolynomial.eval s Q ≠ 0 → Q ≠ 0 :=
    fun h hQ => h (by rw [hQ, map_zero])
  -- the ear data of `G″`: a common non-root `sy` of the three
  obtain ⟨sy, hsy₂, hsya, hsyx⟩ := MvPolynomial.exists_eval_ne_zero₃ (hne0 hQ₂₀) (hne0 hPa'₀)
    hQx₀
  have hrank'' := hQ₂ sy hsy₂
  rw [hPc'] at hrank''
  rw [eval_bind₁_earPicturePoly] at hsya
  have hadmy := hPa _ hsya
  -- the counts
  have hcard : ∀ {k : ℕ} {z : Fin k → α} {H : Graph α β}, V(H) = V₁ ∪ Set.range z →
      Function.Injective z → (∀ i, z i ∉ V₁) → (V(H).ncard : ℤ) = V₁.ncard + k :=
    fun hc hi hz => by rw [hc]; exact_mod_cast Set.ncard_union_range_of_injective hi hz
  set f₁ := (G.induce V₁).deficiency 3
  have hdefG := Graph.deficiency_induce_add_le_of_ear (n := 3) (by decide) (by omega) hcover hinj
    hxV₁ ha hb hpath hsep
  have hs6 : (screwDim 2 : ℤ) = 6 := rfl
  have hb6 : (Graph.bodyBarDim 3 : ℤ) = 6 := rfl
  -- the ear rank law at `G″`: `dim W ≥ m + 1 + f − def(G″)`
  have hC'' : ∀ i, (PanelHingeFramework.ofNormals (k := 2) G'' ends''
      (cfg sy)).toBodyHinge.supportExtensor (e'' i) ≠ 0 :=
    fun i => hadmy.supportExtensor_ne_zero hends'' _ (hpath'' i)
  have hear'' := BodyHingeFramework.finrank_span_rigidityRows_ear_eq
    (PanelHingeFramework.ofNormals (k := 2) G'' ends'' (cfg sy)).toBodyHinge hinj'' hyV₁ ha hb hab
    hpath'' hsep'' hC''
  rw [PanelHingeFramework.toBodyHinge_graph, PanelHingeFramework.ofNormals_graph] at hear''
  rw [hrk₁'' sy, hρ2 sy, span_supportExtensor_comp_eq_map_pointJoin hends'' (cfg sy) e''
    (fun i => pathVertex a y b i.castSucc) (fun i => pathVertex a y b i.succ) hpath'',
    finrank_sup_map_screwComplementIso, ← hρJ] at hear''
  have hW := (Int.self_le_toNat _).trans (Int.ofNat_le.mpr hrank'')
  rw [hear'', hcard hcover'' hinj'' hyV₁, hs6] at hW
  -- put `v` back at `x₂`
  obtain ⟨x₂, hx₂3, hins'⟩ := hQx sy hsyx hadmy
  set st := Function.update (Function.update (Function.update sy (Sum.inl (v, 0)) (x₂ 0))
    (Sum.inl (v, 1)) (x₂ 1)) (Sum.inr v) (x₂ 2) with hst
  have hlt := hins' (fun t j => cfg st (t, j))
    (by rw [earConfig_of_mem_X st hvV₁ hvf hvl hv]; funext j; fin_cases j <;> simp [hst, hx₂3])
    (fun t ht => funext fun j => earConfig_congr (fun i => by simp [hst, ht]) (by simp [hst, ht]) j)
  -- the target `n₀ = m + 2 + f − def(G)` is met at `st`
  set n₀ := ((m : ℤ) + 2 + f₁ - G.deficiency 3).toNat
  have hNt : n₀ ≤ Module.finrank K ↥(ρJ ⊔ Submodule.span K (Set.range fun i : Fin (m + 2) =>
      pointJoin (fun j => MvPolynomial.eval st (P (pathVertex a x b i.castSucc, j)))
        (fun j => MvPolynomial.eval st (P (pathVertex a x b i.succ, j))))) := by
    rw [hfam]
    refine le_trans (le_min_iff.mpr ⟨Int.toNat_le.mpr ?_, Int.toNat_le.mpr ?_⟩) hlt
    · push_cast
      linarith
    · push_cast at hdefG ⊢
      linarith
  obtain ⟨Qs, hQs₀, hQs⟩ := exists_mvPolynomial_le_finrank_sup_span_pointJoin ρJ P
    (fun i : Fin (m + 2) => pathVertex a x b i.castSucc) (fun i => pathVertex a x b i.succ) hNt
  have hPm'₀ : MvPolynomial.eval sstar (MvPolynomial.bind₁ (earPicturePoly V₁ q') Pm) ≠ 0 := by
    rwa [eval_bind₁_earPicturePoly, hpicstar]
  -- the ear data of `G`: a common non-root `s₀`, main for `G`
  obtain ⟨s₀, hs₀a, hs₀b⟩ := MvPolynomial.exists_eval_ne_zero₂ (hne0 hQs₀) (hne0 hPm'₀)
  rw [eval_bind₁_earPicturePoly] at hs₀b
  have hqmain₀ := hmain _ hs₀b
  have hz₀ : earHeight V₁ z₁ xf xl (Set.range x) la lb (earPicture V₁ q' s₀)
      (fun t => s₀ (Sum.inr t)) ∈ G.liftingSpace (earPicture V₁ q' s₀) := by
    subst hxf hxl
    exact Graph.earHeight_mem_liftingSpace (by omega) hcover hinj hxV₁ ha hb hab hpath hsep
      hqmain₀.1 (hz₁s s₀) (hlas s₀) (hlbs s₀) _
  -- the ear rank law at `G`
  have hC : ∀ i, (PanelHingeFramework.ofNormals (k := 2) G ends
      (cfg s₀)).toBodyHinge.supportExtensor (e i) ≠ 0 :=
    fun i => hqmain₀.1.supportExtensor_ne_zero hends _ (hpath i)
  have hear := BodyHingeFramework.finrank_span_rigidityRows_ear_eq
    (PanelHingeFramework.ofNormals (k := 2) G ends (cfg s₀)).toBodyHinge hinj hxV₁ ha hb hab hpath
    hsep hC
  rw [PanelHingeFramework.toBodyHinge_graph, PanelHingeFramework.ofNormals_graph] at hear
  rw [hrk₁ s₀, hρG s₀, span_supportExtensor_comp_eq_map_pointJoin hends (cfg s₀) e
    (fun i => pathVertex a x b i.castSucc) (fun i => pathVertex a x b i.succ) hpath,
    finrank_sup_map_screwComplementIso, ← hρJ] at hear
  have hspan₀ := hQs s₀ hs₀a
  rw [hfam] at hspan₀
  refine Graph.x0Attains_of_exists hV ends hends hqmain₀ hz₀ ?_
  change _ ≤ (Module.finrank K ↥(Submodule.span K (PanelHingeFramework.ofNormals (k := 2) G ends
    (cfg s₀)).toBodyHinge.rigidityRows) : ℤ)
  rw [hear, hcard hcover hinj hxV₁, hs6]
  have h₀ : (m : ℤ) + 2 + f₁ - G.deficiency 3 ≤ (n₀ : ℤ) := Int.self_le_toNat _
  have h₁ := Int.ofNat_le.mpr hspan₀
  push_cast at h₁ ⊢
  linarith

/-! ## The open ear with four interior bodies (`thm:pencil-x0-open-ear-four`) -/

open Classical in
/-- **An open ear with four interior bodies** (`thm:pencil-x0-open-ear-four`). Let `G` satisfy the
standing hypotheses, with an open ear `a − x 0 − x 1 − x 2 − x 3 − b` on `V₁` whose ends may be
adjacent, and let `G″ = G.splitOff (x 1) (x 0) (x 2) (e 1)` be `G` with `x 1` suppressed, the freed
label `e 1` relinked to `x 0 − x 2`. If the general configurations of `G[V₁]` and of `G″` attain, so
does that of `G`.

Proof. `Graph.X0Attains.of_openEar_splitOff`, with the ear `a − x 0 − x 2 − x 3 − b` of `G″`
(`splitOff_ear_four`) and `def₃(G″) ≤ def₃(G)` (`Graph.splitOff_deficiency_le_of_eq_left`). `x 1` is
put back at the point of `exists_insertion_four` once the six joins of the points of `x 0`, `x 2`,
`x 3` and `b` span `Λ²K⁴`: a condition on the ear data that holds off the zero set of a polynomial
nonzero at the ear datum whose four points are those of `linearIndependent_tetra_witness`. -/
theorem _root_.Graph.X0Attains.of_openEar_four [Infinite K] [Finite α] [Finite β]
    {G : Graph α β} (hG : G.IsX0Graph) {V₁ : Set α} {x : Fin 4 → α} {a b : α}
    {e : Fin 5 → β} (hcover : V(G) = V₁ ∪ Set.range x) (hinj : Function.Injective x)
    (hxV₁ : ∀ i, x i ∉ V₁) (ha : a ∈ V₁) (hb : b ∈ V₁) (hab : a ≠ b)
    (hpath : ∀ i : Fin 5,
      G.IsLink (e i) (pathVertex a x b i.castSucc) (pathVertex a x b i.succ))
    (hsep : ∀ f u w, G.IsLink f u w → (∀ i, f ≠ e i) → u ∈ V₁ ∧ w ∈ V₁)
    (h₁ : (G.induce V₁).X0Attains K)
    (h₂ : (G.splitOff (x 1) (x 0) (x 2) (e 1)).X0Attains K) : G.X0Attains K := by
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
  obtain ⟨hcover'', hinj'', hxV₁'', hpath'', hsep''⟩ :=
    splitOff_ear_four hcover hinj hxV₁ ha hb hab hpath hsep
  refine Graph.X0Attains.of_openEar_splitOff hG (by norm_num) hcover hinj hxV₁ ha hb hab hpath
    hsep hcover'' hinj'' hxV₁'' hpath'' hsep''
    (by rintro _ ⟨i, rfl⟩; fin_cases i <;> exact ⟨_, rfl⟩) ⟨1, rfl⟩ (hxV₁ 0) l1 (hpath'' 1)
    (Graph.splitOff_deficiency_le_of_eq_left (n := 3) (by decide) x01 x12.symm l1.symm l2 hdeg2)
    (xf := x 0) (xl := x 3) rfl rfl x01.symm x13 (fun q z la lb ρ _ _ => ?_) h₁ h₂
  -- the six joins of `x 0, x 2, x 3, b` span `Λ²K⁴` at one ear datum, so off a polynomial
  set cfg := earConfig V₁ q z (x 0) (x 3) (Set.range x) la lb
  set P := earPointPoly (K := K) V₁ q z (x 0) (x 3) (Set.range x) la lb
  have hPc : ∀ s p, MvPolynomial.eval s (P p) = cfg s p :=
    eval_earPointPoly V₁ q z (x 0) (x 3) (Set.range x) la lb
  set ut : Fin 6 → α := fun i => ![x 0, x 2, x 3, b] (tetA i) with hut
  set wt : Fin 6 → α := fun i => ![x 0, x 2, x 3, b] (tetB i) with hwt
  have htet : ∀ s, (fun i => pointJoin (fun j => MvPolynomial.eval s (P (ut i, j)))
      (fun j => MvPolynomial.eval s (P (wt i, j)))) = fun i =>
        pointJoin (![fun j => cfg s (x 0, j), fun j => cfg s (x 2, j), fun j => cfg s (x 3, j),
          fun j => cfg s (b, j)] (tetA i)) (![fun j => cfg s (x 0, j), fun j => cfg s (x 2, j),
          fun j => cfg s (x 3, j), fun j => cfg s (b, j)] (tetB i)) := by
    intro s; funext i
    have hpts : ∀ n : Fin 4, (fun j => MvPolynomial.eval s (P (![x 0, x 2, x 3, b] n, j))) =
        ![fun j => cfg s (x 0, j), fun j => cfg s (x 2, j), fun j => cfg s (x 3, j),
          fun j => cfg s (b, j)] n := by
      intro n; simp only [hPc]; fin_cases n <;> rfl
    simp only [hut, hwt]; rw [hpts, hpts]
  have htet₀ : ∃ stet : (α × Fin 2) ⊕ α → K, 6 ≤ Module.finrank K ↥((⊥ : Submodule K
      (ScrewSpace K 2)) ⊔ Submodule.span K (Set.range fun i =>
        pointJoin (fun j => MvPolynomial.eval stet (P (ut i, j)))
          (fun j => MvPolynomial.eval stet (P (wt i, j))))) := by
    set b₀ := q (b, 0)
    set b₁ := q (b, 1)
    set stet : (α × Fin 2) ⊕ α → K := Sum.elim
      (fun p => if p.1 = x 0 then ![b₀, b₁ + 1] p.2 else if p.1 = x 2 then ![b₀, b₁] p.2
        else if p.1 = x 3 then ![b₀ + 1, b₁] p.2 else 0)
      (fun w => if w = x 2 then z b + 1 else 0) with hstet
    refine ⟨stet, ?_⟩
    have hp0 : (fun j => cfg stet (x 0, j)) = ![b₀, b₁ + 1, la ⬝ᵥ ![b₀, b₁ + 1, 1], 1] := by
      rw [earConfig_first stet (hxV₁ 0)]
      funext j; fin_cases j <;> simp [hstet, liftPlane]
    have hp2 : (fun j => cfg stet (x 2, j)) = ![b₀, b₁, z b + 1, 1] := by
      rw [earConfig_of_mem_X stet (hxV₁ 2) x02.symm x23 (Set.mem_range_self 2)]
      funext j; fin_cases j <;> simp [hstet, x02.symm]
    have hp3 : (fun j => cfg stet (x 3, j)) = ![b₀ + 1, b₁, lb ⬝ᵥ ![b₀ + 1, b₁, 1], 1] := by
      rw [earConfig_last stet (hxV₁ 3) x03.symm]
      funext j; fin_cases j <;> simp [hstet, liftPlane, x03.symm, x23.symm]
    have hpb : (fun j => cfg stet (b, j)) = ![b₀, b₁, z b, 1] := by
      funext j; refine (earConfig_of_mem stet hb j).trans ?_
      fin_cases j <;> simp [pencilConfigPoint, b₀, b₁]
    rw [htet, hp0, hp2, hp3, hpb, span_pointJoin_tetra_eq_top
      (linearIndependent_tetra_witness b₀ b₁ (z b) _ _), bot_sup_eq, finrank_top,
      finrank_screwSpace_two]
  obtain ⟨stet, hstet⟩ := htet₀
  obtain ⟨Qt, hQt₀, hQt⟩ := exists_mvPolynomial_le_finrank_sup_span_pointJoin ⊥ P ut wt hstet
  refine ⟨Qt, fun h => hQt₀ (by rw [h, map_zero]), fun s hs _ => ?_⟩
  -- the insertion, at an ear datum off it
  set pt : α → Fin 4 → K := fun w j => cfg s (w, j)
  have h6 := hQt s hs
  rw [htet, bot_sup_eq] at h6
  obtain ⟨x₂, hx₂3, hins⟩ := exists_insertion_four ρ (pt a) (pt (x 0)) (pt (x 2)) (pt (x 3))
    (pt b) rfl rfl (Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le _)
      (finrank_screwSpace_two (K := K) ▸ h6)))
  refine ⟨x₂, hx₂3, fun p hp1 hpne => ?_⟩
  have ha1 : a ≠ x 1 := (hax 1).symm
  have hb1 : b ≠ x 1 := (hbx 1).symm
  have e4 : (fun i : Fin (3 + 1) =>
      pointJoin (fun j => cfg s (pathVertex a ![x 0, x 2, x 3] b i.castSucc, j))
        (fun j => cfg s (pathVertex a ![x 0, x 2, x 3] b i.succ, j))) =
      ![pointJoin (pt a) (pt (x 0)), pointJoin (pt (x 0)) (pt (x 2)),
        pointJoin (pt (x 2)) (pt (x 3)), pointJoin (pt (x 3)) (pt b)] := by
    funext i; fin_cases i <;> rfl
  have e5 : (fun i : Fin (3 + 2) =>
      pointJoin (p (pathVertex a x b i.castSucc)) (p (pathVertex a x b i.succ))) =
      ![pointJoin (pt a) (pt (x 0)), pointJoin (pt (x 0)) x₂, pointJoin x₂ (pt (x 2)),
        pointJoin (pt (x 2)) (pt (x 3)), pointJoin (pt (x 3)) (pt b)] := by
    funext i
    fin_cases i
    · change pointJoin (p a) (p (x 0)) = _
      rw [hpne _ ha1, hpne _ x01]; rfl
    · change pointJoin (p (x 0)) (p (x 1)) = _
      rw [hpne _ x01, hp1]; rfl
    · change pointJoin (p (x 1)) (p (x 2)) = _
      rw [hp1, hpne _ x12.symm]; rfl
    · change pointJoin (p (x 2)) (p (x 3)) = _
      rw [hpne _ x12.symm, hpne _ x13.symm]; rfl
    · change pointJoin (p (x 3)) (p b) = _
      rw [hpne _ x13.symm, hpne _ hb1]; rfl
  rw [e4, e5]
  repeat rw [Matrix.range_cons]
  rw [Matrix.range_empty, Set.union_empty]
  exact hins

/-! ## The open ear with three interior bodies (`thm:pencil-x0-open-ear-three`) -/

open Classical in
/-- **An open ear with three interior bodies** (`thm:pencil-x0-open-ear-three`). Let `G` satisfy the
standing hypotheses, with an open ear `a − x 0 − x 1 − x 2 − b` on `V₁` whose ends may be adjacent,
and let `G″ = G.splitOff (x 1) (x 0) (x 2) (e 1)` be `G` with `x 1` suppressed, the freed label
`e 1` relinked to `x 0 − x 2`. If the general configurations of `G[V₁]` and of `G″` attain, so does
that of `G`.

Proof. `Graph.X0Attains.of_openEar_splitOff`, with the ear `a − x 0 − x 2 − b` of `G″`
(`splitOff_ear_three`) and `def₃(G″) ≤ def₃(G)` (`Graph.splitOff_deficiency_le_of_eq_left`). `x 1`
is put back at the point of `exists_insertion_three`, which asks that the span `W` of `ρ` and the
joins of the ear of `G″` be `Λ²K⁴` whenever it contains every line through the point `y₁` of `x 0`
and every line through the point `y₃` of `x 2`, the two stars. Over the base data, either every
relative screw pairs to zero with every line joining the planes `la` at `a` and `lb` at `b`, and
then `W` does not contain both stars (`not_star_sup_star_le_of_klein`); or some `c ∈ ρ` does not,
and then `⟨c, y₁ ∧ y₃⟩ ≠ 0` is a further condition on the ear data, a span bound against the kernel
of `⟨c, ·⟩` that holds at a pair of affine points (`exists_klein_liftPlane_affine_ne_zero`), under
which a `W` containing both stars is `Λ²K⁴` (`eq_top_of_star_sup_star_le`). -/
theorem _root_.Graph.X0Attains.of_openEar_three [Infinite K] [Finite α] [Finite β]
    {G : Graph α β} (hG : G.IsX0Graph) {V₁ : Set α} {x : Fin 3 → α} {a b : α}
    {e : Fin 4 → β} (hcover : V(G) = V₁ ∪ Set.range x) (hinj : Function.Injective x)
    (hxV₁ : ∀ i, x i ∉ V₁) (ha : a ∈ V₁) (hb : b ∈ V₁) (hab : a ≠ b)
    (hpath : ∀ i : Fin 4,
      G.IsLink (e i) (pathVertex a x b i.castSucc) (pathVertex a x b i.succ))
    (hsep : ∀ f u w, G.IsLink f u w → (∀ i, f ≠ e i) → u ∈ V₁ ∧ w ∈ V₁)
    (h₁ : (G.induce V₁).X0Attains K)
    (h₂ : (G.splitOff (x 1) (x 0) (x 2) (e 1)).X0Attains K) : G.X0Attains K := by
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
  obtain ⟨hcover'', hinj'', hxV₁'', hpath'', hsep''⟩ :=
    splitOff_ear_three hcover hinj hxV₁ ha hb hab hpath hsep
  refine Graph.X0Attains.of_openEar_splitOff hG le_rfl hcover hinj hxV₁ ha hb hab hpath
    hsep hcover'' hinj'' hxV₁'' hpath'' hsep''
    (by rintro _ ⟨i, rfl⟩; fin_cases i <;> exact ⟨_, rfl⟩) ⟨1, rfl⟩ (hxV₁ 0) l1 (hpath'' 1)
    (Graph.splitOff_deficiency_le_of_eq_left (n := 3) (by decide) x01 x12.symm l1.symm l2 hdeg2)
    (xf := x 0) (xl := x 2) rfl rfl x01.symm x12 (fun q z la lb ρ hza hzb => ?_) h₁ h₂
  set cfg := earConfig V₁ q z (x 0) (x 2) (Set.range x) la lb
  set P := earPointPoly (K := K) V₁ q z (x 0) (x 2) (Set.range x) la lb
  -- the points of the ear data, on the planes `la` and `lb` at the ends
  set pt : ((α × Fin 2) ⊕ α → K) → α → Fin 4 → K := fun s w j => cfg s (w, j) with hpt
  have hevpt : ∀ s w, (fun j => MvPolynomial.eval s (P (w, j))) = pt s w :=
    fun s w => funext fun j => eval_earPointPoly V₁ q z (x 0) (x 2) (Set.range x) la lb s (w, j)
  have hcV₁ : ∀ s w, w ∈ V₁ → ∀ j, cfg s (w, j) = pencilConfigPoint q z w j :=
    fun s w hw j => earConfig_of_mem s hw j
  have hpta : ∀ s, pt s a = liftPlane la (pencilPicturePoint q a) := by
    intro s; funext j; simp only [hpt, hcV₁ s a ha]
    fin_cases j <;> simp [pencilConfigPoint, liftPlane, pencilPicturePoint, hza]
  have hptb : ∀ s, pt s b = liftPlane lb (pencilPicturePoint q b) := by
    intro s; funext j; simp only [hpt, hcV₁ s b hb]
    fin_cases j <;> simp [pencilConfigPoint, liftPlane, pencilPicturePoint, hzb]
  have hpt0 : ∀ s, pt s (x 0) = liftPlane la ![s (Sum.inl (x 0, 0)), s (Sum.inl (x 0, 1)), 1] :=
    fun s => earConfig_first s (hxV₁ 0)
  have hpt2 : ∀ s, pt s (x 2) = liftPlane lb ![s (Sum.inl (x 2, 0)), s (Sum.inl (x 2, 1)), 1] :=
    fun s => earConfig_last s (hxV₁ 2) x02.symm
  -- the case split on `ρ`, made before the ear data
  have hextra : ∃ Qx : MvPolynomial ((α × Fin 2) ⊕ α) K, Qx ≠ 0 ∧
      ∀ s, MvPolynomial.eval s Qx ≠ 0 → LinearIndependent K ![pt s (x 0), pt s (x 2)] →
        star (pt s (x 0)) ⊔ star (pt s (x 2)) ≤ ρ ⊔ Submodule.span K
          {pointJoin (pt s a) (pt s (x 0)), pointJoin (pt s (x 0)) (pt s (x 2)),
            pointJoin (pt s (x 2)) (pt s b)} →
        ρ ⊔ Submodule.span K {pointJoin (pt s a) (pt s (x 0)),
          pointJoin (pt s (x 0)) (pt s (x 2)), pointJoin (pt s (x 2)) (pt s b)} = ⊤ := by
    by_cases hB : ∀ c ∈ ρ, ∀ u v, kleinLin (pointJoin (liftPlane la u) (liftPlane lb v)) c = 0
    · -- every relative screw pairs to zero with every line joining the two planes: `dim W ≤ 3`, so
      -- `W` does not contain both stars
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
    · -- some `c ∈ ρ` pairs to a nonzero value with a line joining the two planes: ask
      -- `⟨c, y₁ ∧ y₃⟩ ≠ 0` of the ear data
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
      refine ⟨Qx, fun h => hQx₀ (by rw [h, map_zero]), fun s hs hli hle => ?_⟩
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
  -- `x 1` is put back next to `y₁` or `y₃`, or at `y₁` when `W = Λ²K⁴`
  refine ⟨Qx, hQx₀, fun s hs hadm => ?_⟩
  obtain ⟨x₂, hx₂3, hins⟩ := exists_insertion_three ρ (pt s a) (pt s (x 0)) (pt s (x 2))
    (pt s b) rfl rfl (hQx s hs
      (linearIndependent_pencilConfigPoint_pair _ (hadm.1 _ _ _ (hpath'' 1))))
  refine ⟨x₂, hx₂3, fun p hp1 hpne => ?_⟩
  have ha1 : a ≠ x 1 := (hax 1).symm
  have hb1 : b ≠ x 1 := (hbx 1).symm
  have e3 : (fun i : Fin (2 + 1) =>
      pointJoin (fun j => cfg s (pathVertex a ![x 0, x 2] b i.castSucc, j))
        (fun j => cfg s (pathVertex a ![x 0, x 2] b i.succ, j))) =
      ![pointJoin (pt s a) (pt s (x 0)), pointJoin (pt s (x 0)) (pt s (x 2)),
        pointJoin (pt s (x 2)) (pt s b)] := by
    funext i; fin_cases i <;> rfl
  have e4 : (fun i : Fin (2 + 2) =>
      pointJoin (p (pathVertex a x b i.castSucc)) (p (pathVertex a x b i.succ))) =
      ![pointJoin (pt s a) (pt s (x 0)), pointJoin (pt s (x 0)) x₂, pointJoin x₂ (pt s (x 2)),
        pointJoin (pt s (x 2)) (pt s b)] := by
    funext i
    fin_cases i
    · change pointJoin (p a) (p (x 0)) = _
      rw [hpne _ ha1, hpne _ x01]; rfl
    · change pointJoin (p (x 0)) (p (x 1)) = _
      rw [hpne _ x01, hp1]; rfl
    · change pointJoin (p (x 1)) (p (x 2)) = _
      rw [hp1, hpne _ x12.symm]; rfl
    · change pointJoin (p (x 2)) (p b) = _
      rw [hpne _ x12.symm, hpne _ hb1]; rfl
  rw [e3, e4]
  repeat rw [Matrix.range_cons]
  rw [Matrix.range_empty, Set.union_empty]
  exact hins

end CombinatorialRigidity.Molecular
