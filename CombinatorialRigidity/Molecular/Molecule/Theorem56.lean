/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.AlgebraicInduction.Theorem55
import CombinatorialRigidity.Molecular.Molecule.GeneralPosition4

/-!
# KT Theorem 5.6 in `ℝ³`, with the poles in general position

The panel-hinge realization of `lem:theorem-56-general-position`, as
`sec:molecule-modelling-general-position` presents it: a simple graph `G` that spans a nonempty set
of bodies, with more than `6(|V| - 1)` labels, has a panel-hinge realization in `ℝ³` at the rank of
KT Theorem 5.6, `dim Z = D + def(G̃)`, whose normals are in general position up to order four
(`IsGeneralPosition4`, `GeneralPosition4.lean`). Their poles are then in general position up to
order four, as the square-graph dictionary (`thm:molecular-iff-square-bar-joint`) needs of the
centres of the molecular framework on them. Katoh and Tanigawa need only a nonparallel realization,
whose panels meet pairwise in lines, and obtain it by a projective transformation (KT pp. 670–671).

`exists_rankHypothesis_isGeneralPosition4` splits on the number of bodies. A single body (`|V| = 1`)
has no edge, and the moment-curve normals serve. On two or more bodies,
`exists_rankHypothesis_isGeneralPosition4_of_two_le` moves the normals of a realization of KT
Theorem 5.6 into general position without lowering the rank:

* `rankHypothesis_genuine_recordsLinks_of_theorem_55_gen` (`n = 3`, `k = 2`;
  `thm:theorem-55-6-genuine`) gives a link-recording realization `Q₀` with nondegenerate hinges at
  `dim Z = D + def(G̃)`, which we view as `ofNormals G Q₀.ends q₀` at its own normals `q₀`;
* rank–nullity for the rigidity rows (`finrank_span_rigidityRows_add_finrank_infinitesimalMotions`)
  turns `dim Z = D + def` into the rank `D(|V| − 1) − def` of the rows of `Q₀`, and
  `exists_rankPolynomial_of_le_finrank_linking` (`lem:rank-polynomial-of-le-finrank`) gives a
  polynomial `Q_rk` that does not vanish at `q₀` and at whose non-roots the rows have at least that
  rank;
* `exists_generalPosition4_polynomial` gives the polynomial `Q_gp4` that tests general position up
  to order four;
* the product `Q_rk · Q_gp4` is nonzero, so it has a non-root `q*`
  (`MvPolynomial.exists_eval_ne_zero`). At `q*` the rows have rank at least `D(|V| − 1) − def` (by
  `Q_rk`) and at most `D(|V| − 1) − def` (`finrank_span_rigidityRows_add_deficiency_le`,
  `lem:relative-deficiency-rank-bound`, as the hinges are nondegenerate by `IsGeneralPosition4` and
  `IsLink.ne`), so `RankHypothesis (def)` holds there, with the normals in general position up to
  order four.

## Main results

* `PanelHingeFramework.exists_rankHypothesis_isGeneralPosition4`: the realization of
  `lem:theorem-56-general-position`, on a nonempty set of bodies.
* `PanelHingeFramework.exists_rankHypothesis_isGeneralPosition4_of_two_le`: its case of two or more
  bodies.
-/

namespace CombinatorialRigidity.Molecular

open scoped Graph

open MvPolynomial

variable {α β : Type*}

namespace PanelHingeFramework

set_option linter.unusedDecidableInType false in
/-- **KT Theorem 5.6 in `ℝ³` with the poles in general position, on two or more bodies** (a step of
`lem:theorem-56-general-position`: its case `2 ≤ |V|`; KT Theorem 5.6, Katoh and Tanigawa 2011,
§5.2, p. 670): for a simple graph `G` that spans two or more bodies in `ℝ³`, with more than
`6(|V| - 1)` labels, there is a panel-hinge realization `Q` on `G` that

* records a `G`-link on every `G`-link (`hends`);
* has a nonzero supporting extensor on every `G`-link (nondegenerate hinges);
* realizes the target rank `dim Z(G, Q) = D + def(G̃)` (`RankHypothesis (G.deficiency 3)`); and
* has normals in general position up to order four (`IsGeneralPosition4`): every normal has
  nonvanishing last coordinate and every `≤ 4`-normal subfamily is linearly independent.

The poles of its normals are then in general position up to order four, as the square-graph
dictionary (`thm:molecular-iff-square-bar-joint`) needs. The proof takes a non-root of the product
of the rank polynomial of `exists_rankPolynomial_of_le_finrank_linking`, at the normals of the
realization of `rankHypothesis_genuine_recordsLinks_of_theorem_55_gen`, and the polynomial of
`exists_generalPosition4_polynomial` (`MvPolynomial.exists_eval_ne_zero`); see the file header.

`[DecidableEq β]` is an instance argument of
`rankHypothesis_genuine_recordsLinks_of_theorem_55_gen`, which the proof calls, and does not appear
in the conclusion; hence the `unusedDecidableInType` suppression. -/
theorem exists_rankHypothesis_isGeneralPosition4_of_two_le
    [Nonempty α] [Finite α] [Finite β] [DecidableEq β]
    (hcard : 6 * (Nat.card α - 1) < Nat.card β)
    (G : Graph α β) (hV : 2 ≤ V(G).ncard) (hspan : V(G) = Set.univ) (hSimple : G.Simple) :
    ∃ Q : PanelHingeFramework ℝ 2 α β, Q.graph = G ∧
      (∀ e u v, G.IsLink e u v → G.IsLink e (Q.ends e).1 (Q.ends e).2) ∧
      (∀ e u v, G.IsLink e u v → Q.toBodyHinge.supportExtensor e ≠ 0) ∧
      Q.toBodyHinge.RankHypothesis (G.deficiency 3) ∧
      Q.IsGeneralPosition4 := by
  classical
  have hloop : G.Loopless := hSimple.toLoopless
  -- Numerics for `n = 3`, `k = 2`.
  have hD : (3 : ℕ) ≤ Graph.bodyBarDim 3 := Graph.three_le_bodyBarDim_of_two_le (by norm_num)
  have hn : Graph.bodyBarDim 3 = screwDim 2 := Graph.bodyBarDim_eq_screwDim_sub_one (by norm_num)
  have hfresh : ∀ (c : ℤ) (G' : Graph α β), G'.IsMinimalKDof 3 c → ∃ e₀ : β, e₀ ∉ E(G') :=
    Graph.freshEdgeSupply_of_card_lt (by omega) (by simpa [Graph.bodyBarDim] using hcard)
  -- Step 1: KT Theorem 5.6 with nondegenerate hinges and a link-recording selector.
  obtain ⟨Q0, hQ0g, hQ0ends, hQ0C, hQ0rank⟩ :=
    rankHypothesis_genuine_recordsLinks_of_theorem_55_gen
      (K := ℝ) (k := 2) (n := 3) (by norm_num) hD hn hfresh G hV hspan hSimple
  -- View `Q0` as the free-normal framework at its own normals `q₀ = fun p => Q0.normal p.1 p.2`.
  have hself : ofNormals (k := 2) G Q0.ends (fun p => Q0.normal p.1 p.2) = Q0 := by
    rw [← hQ0g]; rfl
  -- `|V| ≥ 1` facts and the body-count reconciliation `Nat.card α = |V(G)|`.
  have hVGne : V(G).Nonempty := by rw [hspan]; exact Set.univ_nonempty
  have h1V : 1 ≤ V(G).ncard := by omega
  have hcardα : Nat.card α = V(G).ncard := by rw [hspan, Set.ncard_univ]
  -- The exact row count of `Q0` at its own normals: `finrank (span rows) = D(|V|−1) − def`.
  have hrank0 : (Module.finrank ℝ (Submodule.span ℝ Q0.toBodyHinge.rigidityRows) : ℤ)
      = screwDim 2 * ((V(G).ncard : ℤ) - 1) - G.deficiency 3 := by
    have hcompl := Q0.toBodyHinge.finrank_span_rigidityRows_add_finrank_infinitesimalMotions
    rw [hcardα] at hcompl
    have hZ : (Module.finrank ℝ Q0.toBodyHinge.infinitesimalMotions : ℤ)
        = screwDim 2 + G.deficiency 3 := hQ0rank
    zify [h1V] at hcompl
    rw [mul_sub, mul_one]
    linarith [hcompl, hZ]
  -- Step 2: the rank polynomial, nonzero at `q₀`.
  obtain ⟨Q_rk, hQ_rk0, hQ_rk⟩ :=
    exists_rankPolynomial_of_le_finrank_linking G Q0.ends hQ0ends
      (q₀ := fun p => Q0.normal p.1 p.2)
      (fun e _ => by rw [hself]; exact hQ0C e)
      (N := Module.finrank ℝ (Submodule.span ℝ Q0.toBodyHinge.rigidityRows))
      (le_of_eq (by rw [hself]))
  -- Step 3: the order-four general-position avoidance polynomial.
  obtain ⟨Q_gp4, hQgp4_moment, hQgp4_pred⟩ :=
    exists_generalPosition4_polynomial G Q0.ends
  -- Both polynomials are nonzero: `Q_rk` by its `q₀`-value, `Q_gp4` by its moment-curve value.
  have hQ_rk_ne : Q_rk ≠ 0 := fun h => hQ_rk0 (by rw [h, map_zero])
  have hQ_gp4_ne : Q_gp4 ≠ 0 := by
    obtain ⟨f, hf⟩ := Countable.exists_injective_nat α
    refine fun h => hQgp4_moment (fun a => (f a : ℝ) + 1) ?_ (fun a => by positivity)
      (by rw [h, map_zero])
    exact fun a b hab => hf (by exact_mod_cast add_right_cancel hab)
  -- Step 4: a non-root of the product (`MvPolynomial.exists_eval_ne_zero`) is a non-root of both.
  obtain ⟨q_star, hq_star⟩ := MvPolynomial.exists_eval_ne_zero (mul_ne_zero hQ_rk_ne hQ_gp4_ne)
  rw [map_mul] at hq_star
  have hq_rk : eval q_star Q_rk ≠ 0 := fun h => hq_star (by rw [h]; ring)
  have hq_gp4 : eval q_star Q_gp4 ≠ 0 := fun h => hq_star (by rw [h]; ring)
  -- The realization at `q_star`, its general position up to order four, and its nondegenerate
  -- hinges.
  have hgp4 : (ofNormals (k := 2) G Q0.ends q_star).IsGeneralPosition4 := hQgp4_pred q_star hq_gp4
  have hgp2 : (ofNormals (k := 2) G Q0.ends q_star).IsGeneralPosition := hgp4.isGeneralPosition
  have hC : ∀ e u v, G.IsLink e u v →
      (ofNormals (k := 2) G Q0.ends q_star).toBodyHinge.supportExtensor e ≠ 0 := by
    intro e u v hl
    refine supportExtensor_ne_zero_of_isGeneralPosition
      (ofNormals (k := 2) G Q0.ends q_star) hgp2 ?_
    rw [ofNormals_ends]
    exact (hQ0ends e u v hl).ne
  -- Lower bound at `q*` (rank polynomial) and upper bound at `q*` (deficiency bound).
  have hlb := hQ_rk q_star hq_rk
  have hub := BodyHingeFramework.finrank_span_rigidityRows_add_deficiency_le
    (ofNormals (k := 2) G Q0.ends q_star).toBodyHinge hn hVGne (fun e u v h => hC e u v h)
  simp only [toBodyHinge_graph, ofNormals_graph] at hub
  -- The two bounds pinch the row count to the exact value, giving back `RankHypothesis (def)`.
  have hrankeq : (Module.finrank ℝ (Submodule.span ℝ
      (ofNormals (k := 2) G Q0.ends q_star).toBodyHinge.rigidityRows) : ℤ)
      = screwDim 2 * ((V(G).ncard : ℤ) - 1) - G.deficiency 3 := by
    refine le_antisymm hub ?_
    rw [← hrank0]; exact_mod_cast hlb
  refine ⟨ofNormals (k := 2) G Q0.ends q_star, ofNormals_graph G Q0.ends q_star,
    ?_, hC, ?_, hgp4⟩
  · intro e u v he; rw [ofNormals_ends]; exact hQ0ends e u v he
  · -- `RankHypothesis (def)`: `dim Z = D + def` from the complement identity + the exact row count.
    change (Module.finrank ℝ
        (ofNormals (k := 2) G Q0.ends q_star).toBodyHinge.infinitesimalMotions : ℤ)
      = screwDim 2 + G.deficiency 3
    have hcompl := BodyHingeFramework.finrank_span_rigidityRows_add_finrank_infinitesimalMotions
      (ofNormals (k := 2) G Q0.ends q_star).toBodyHinge
    rw [hcardα] at hcompl
    zify [h1V] at hcompl
    rw [mul_sub, mul_one] at hrankeq
    linarith [hcompl, hrankeq]

set_option linter.unusedDecidableInType false in
/-- **KT Theorem 5.6 in `ℝ³` with the poles in general position**
(`lem:theorem-56-general-position`; KT Theorem 5.6, Katoh and Tanigawa 2011, §5.2, p. 670): for a
simple graph `G` that spans a nonempty set of bodies in `ℝ³`, with more than `6(|V| - 1)` labels,
there is a panel-hinge realization `Q` on `G` that

* records a `G`-link on every `G`-link (`hends`);
* has a nonzero supporting extensor on every `G`-link (nondegenerate hinges);
* realizes the target rank `dim Z(G, Q) = D + def(G̃)` (`RankHypothesis (G.deficiency 3)`); and
* has normals in general position up to order four (`IsGeneralPosition4`).

The poles of its normals are then in general position up to order four, as the square-graph
dictionary (`thm:molecular-iff-square-bar-joint`) needs.

The proof splits on the number of bodies. On two or more, it is
`exists_rankHypothesis_isGeneralPosition4_of_two_le`. On one (`|V| = 1`, so `α` is a subsingleton),
`G` is edgeless (simple ⇒ loopless, and a subsingleton has no distinct endpoints, so `IsLink.ne`
refutes every link), so `def(G̃) = 0` (`Graph.deficiency_of_edgeSet_empty`), the framework is
infinitesimally rigid (`rankHypothesis_zero_iff` and subsingleton constancy), and the conjuncts on
`hends` and on the hinges hold vacuously. The moment-curve normals at the constant parameter `1` are
in general position up to order four by `exists_generalPosition4_polynomial` at the moment curve
(nonvanishing last coordinate, and every `≤ 4`-subfamily, here at most a singleton, independent).

`[DecidableEq β]` is an instance argument of `exists_rankHypothesis_isGeneralPosition4_of_two_le`,
which the proof calls, and does not appear in the conclusion; hence the `unusedDecidableInType`
suppression. -/
theorem exists_rankHypothesis_isGeneralPosition4
    [Nonempty α] [Finite α] [Finite β] [DecidableEq β]
    (hcard : 6 * (Nat.card α - 1) < Nat.card β)
    (G : Graph α β) (hne : V(G).Nonempty) (hspan : V(G) = Set.univ) (hSimple : G.Simple) :
    ∃ Q : PanelHingeFramework ℝ 2 α β, Q.graph = G ∧
      (∀ e u v, G.IsLink e u v → G.IsLink e (Q.ends e).1 (Q.ends e).2) ∧
      (∀ e u v, G.IsLink e u v → Q.toBodyHinge.supportExtensor e ≠ 0) ∧
      Q.toBodyHinge.RankHypothesis (G.deficiency 3) ∧
      Q.IsGeneralPosition4 := by
  by_cases hV2 : 2 ≤ V(G).ncard
  · exact exists_rankHypothesis_isGeneralPosition4_of_two_le hcard G hV2 hspan hSimple
  · -- Single-body branch: `|V| = 1`, so `α` is a subsingleton and `G` is edgeless.
    classical
    have : Fintype α := Fintype.ofFinite α
    have hloop : G.Loopless := hSimple.toLoopless
    have hpos : 0 < V(G).ncard := (Set.ncard_pos (Set.toFinite _)).2 hne
    have hV1 : V(G).ncard = 1 := by omega
    have hsub : Subsingleton α := by
      rw [hspan, Set.ncard_univ, Nat.card_eq_fintype_card] at hV1
      exact Fintype.card_le_one_iff_subsingleton.mp (by omega)
    -- A subsingleton loopless graph has no `G`-links, hence no edges.
    have hnolink : ∀ e u v, ¬ G.IsLink e u v := fun _ u v hl => hl.ne (Subsingleton.elim u v)
    have hE : E(G) = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro e he
      obtain ⟨u, v, hl⟩ := Graph.exists_isLink_of_mem_edgeSet he
      exact hnolink e u v hl
    -- `def(G̃) = 0` (edgeless graph on a single body).
    have hdef0 : G.deficiency 3 = 0 := by rw [Graph.deficiency_of_edgeSet_empty hE, hV1]; simp
    -- The moment-curve normals at the constant parameter `1` are in general position (order four).
    set ends : β → α × α := fun _ => (Classical.arbitrary α, Classical.arbitrary α) with hends
    have hinj : Function.Injective (fun _ : α => (1 : ℝ)) := fun a b _ => Subsingleton.elim a b
    obtain ⟨Q_gp4, hmoment, hpred⟩ := exists_generalPosition4_polynomial G ends
    set q : α × Fin 4 → ℝ := fun p => PanelHingeFramework.momentCurve (1 : ℝ) p.2 with hq
    have hgp4 : (ofNormals (k := 2) G ends q).IsGeneralPosition4 := by
      refine hpred q ?_
      rw [hq]; exact hmoment (fun _ => 1) hinj (fun _ => one_ne_zero)
    -- Rigidity is automatic on a subsingleton (any two bodies coincide).
    have hrig : (ofNormals (k := 2) G ends q).toBodyHinge.IsInfinitesimallyRigid := by
      rw [← BodyHingeFramework.isInfinitesimallyRigidOn_univ_iff]
      intro S _ u _ v _; rw [Subsingleton.elim u v]
    refine ⟨ofNormals (k := 2) G ends q, ofNormals_graph G ends q, ?_, ?_, ?_, hgp4⟩
    · exact fun e u v hl => absurd hl (hnolink e u v)
    · exact fun e u v hl => absurd hl (hnolink e u v)
    · rw [hdef0]; exact (BodyHingeFramework.rankHypothesis_zero_iff _).mpr hrig

end PanelHingeFramework

end CombinatorialRigidity.Molecular
