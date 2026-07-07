/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.AlgebraicInduction.Theorem55
import CombinatorialRigidity.Molecular.Molecule.GeneralPosition4

/-!
# Theorem 5.6 at `d = 3`, general-position form (Phase 25, leaf W6)

Phase 25 (`sec:molecule-modelling`, `lem:theorem-56-general-position`, leaf W6). The square-graph
dictionary (`thm:molecular-iff-square-bar-joint`) consumes a panel realization whose normals are in
general position *up to order four* (`PanelHingeFramework.IsGeneralPosition4`,
`GeneralPosition4.lean`). The landed genuine Theorem-5.6 producer
(`rankHypothesis_genuine_recordsLinks_of_theorem_55_gen`, `Theorem55.lean`) realizes the target rank
`dim Z = D + def(G̃)` but says nothing about the normals; this file strengthens that realization to
one whose normals are in general position up to order four, via the algebraic-induction genericity
device (§2.4 of `notes/Phase25-design.md`; Katoh–Tanigawa 2011 p. 671, the word "nonparallel").

The assembly (the `2 ≤ |V|` main branch — the `|V| = 1` branch and the `≥ 1`-body dispatch that
closes the blueprint node are separate):

1. `rankHypothesis_genuine_recordsLinks_of_theorem_55_gen` (`n = 3`, `k = 2`) produces a genuine
   link-recording realization `Q₀` at `dim Z = D + def(G̃)`, which we view as
   `ofNormals G Q₀.ends q₀` at its own normals `q₀`;
2. the rigidity-row/motion complement identity turns `dim Z = D + def` into an exact row count
   `finrank (span rigidityRows) = D(|V|−1) − def`, fed to the deficiency-graded rank polynomial
   `exists_rankPolynomial_of_le_finrank_linking` → `Q_rk`;
3. the order-four general-position avoidance polynomial `exists_generalPosition4_polynomial`
   → `Q_gp4`;
4. an algebraically-independent-over-`ℚ` seed `q*` (`exists_injective_algebraicIndependent_real`)
   is a simultaneous non-root of the rational `Q_rk` and `Q_gp4`, so at `q*` the realization has row
   count `≥ D(|V|−1) − def` (from `Q_rk`) and `≤ D(|V|−1) − def` (the genuine-hinge upper bound
   `finrank_span_rigidityRows_add_deficiency_le`, genuine hinges from `IsGeneralPosition4` and
   `IsLink.ne`), hence `= `, giving back `RankHypothesis (def)` — now with general-position normals.

Scope is `ℝ³` (`k = 2`, `Fin 4`) throughout, matching the phase (`notes/Phase25.md`).

See `notes/Phase25-design.md` §2.4 (leaf W6) and `blueprint/src/chapter/molecule-modelling.tex`
(`lem:theorem-56-general-position`).

## Main results

* `PanelHingeFramework.exists_rankHypothesis_isGeneralPosition4_of_two_le` — the general-position
  form of Theorem 5.6 for a simple spanning graph on `≥ 2` bodies in `ℝ³`: a panel-hinge realization
  at `dim Z = D + def(G̃)` whose normals are in general position up to order four.
-/

namespace CombinatorialRigidity.Molecular

open scoped Graph

open MvPolynomial

variable {α β : Type*}

namespace PanelHingeFramework

set_option linter.unusedDecidableInType false in
/-- **Theorem 5.6 at `d = 3`, general-position form, `≥ 2`-body branch**
(`lem:theorem-56-general-position`, `2 ≤ |V|` branch; Katoh–Tanigawa 2011 §5.2 Theorem 5.6 + the
p. 671 "nonparallel" strengthening; Phase 25 leaf W6, §2.4 of `notes/Phase25-design.md`). For a
simple spanning graph `G` on `≥ 2` bodies in `ℝ³` with enough hinge labels, there is a panel-hinge
realization `Q` on `G` that

* records a genuine `G`-link on every `G`-link (`hends`);
* has a nonzero supporting extensor on every `G`-link (genuine hinges);
* realizes the target rank `dim Z(G, Q) = D + def(G̃)` (`RankHypothesis (G.deficiency 3)`); and
* has normals in general position up to order four (`IsGeneralPosition4`): every normal has
  nonvanishing last coordinate and every `≤ 4`-normal subfamily is linearly independent.

This is the realization the square-graph dictionary (`thm:molecular-iff-square-bar-joint`) consumes.
The proof composes the genuine link-recording producer
(`rankHypothesis_genuine_recordsLinks_of_theorem_55_gen`) with the deficiency-graded rank polynomial
(`exists_rankPolynomial_of_le_finrank_linking`) and the order-four avoidance polynomial
(`exists_generalPosition4_polynomial`), certified simultaneously nonzero at an
algebraically-independent seed (`exists_injective_algebraicIndependent_real`); see the file header.

`[DecidableEq β]` is used in the proof (the genuine producer and its spanning strip carry it as an
instance argument) but does not appear in the conclusion's type; the `unusedDecidableInType`
suppression is correct here, exactly as in `rankHypothesis_of_theorem_55_gen`. -/
theorem exists_rankHypothesis_isGeneralPosition4_of_two_le
    [Nonempty α] [Finite α] [Finite β] [DecidableEq β]
    (hcard : 6 * (Nat.card α - 1) < Nat.card β)
    (G : Graph α β) (hV : 2 ≤ V(G).ncard) (hspan : V(G) = Set.univ) (hSimple : G.Simple) :
    ∃ Q : PanelHingeFramework 2 α β, Q.graph = G ∧
      (∀ e u v, G.IsLink e u v → G.IsLink e (Q.ends e).1 (Q.ends e).2) ∧
      (∀ e u v, G.IsLink e u v → Q.toBodyHinge.supportExtensor e ≠ 0) ∧
      Q.toBodyHinge.RankHypothesis (G.deficiency 3) ∧
      Q.IsGeneralPosition4 := by
  classical
  haveI hloop : G.Loopless := hSimple.toLoopless
  -- Numerics for `n = 3`, `k = 2`.
  have hD : (6 : ℕ) ≤ Graph.bodyBarDim 3 := Graph.six_le_bodyBarDim (by norm_num)
  have hn : Graph.bodyBarDim 3 = screwDim 2 := Graph.bodyBarDim_eq_screwDim_sub_one (by norm_num)
  have hfresh : ∀ (c : ℤ) (G' : Graph α β), G'.IsMinimalKDof 3 c → ∃ e₀ : β, e₀ ∉ E(G') :=
    Graph.freshEdgeSupply_of_card_lt (by omega) (by simpa [Graph.bodyBarDim] using hcard)
  -- Step 1: the genuine link-recording Theorem-5.6 producer (the F1 fix).
  obtain ⟨Q0, hQ0g, hQ0ends, hQ0C, hQ0rank⟩ :=
    rankHypothesis_genuine_recordsLinks_of_theorem_55_gen
      (k := 2) (n := 3) (by norm_num) hD hn hfresh G hV hspan hSimple
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
  -- Step 2: the deficiency-graded rank polynomial, seeded at `q₀`.
  obtain ⟨Q_rk, hQ_rk0, hQ_rkrat, hQ_rk⟩ :=
    exists_rankPolynomial_of_le_finrank_linking G Q0.ends hQ0ends
      (q₀ := fun p => Q0.normal p.1 p.2)
      (fun e _ => by rw [hself]; exact hQ0C e)
      (N := Module.finrank ℝ (Submodule.span ℝ Q0.toBodyHinge.rigidityRows))
      (le_of_eq (by rw [hself]))
  -- Step 3: the order-four general-position avoidance polynomial.
  obtain ⟨Q_gp4, hQgp4_moment, hQgp4_rat, hQgp4_pred⟩ :=
    exists_generalPosition4_polynomial G Q0.ends
  -- Both polynomials are nonzero: `Q_rk` by its `q₀`-value, `Q_gp4` by its moment-curve value.
  have hQ_rk_ne : Q_rk ≠ 0 := fun h => hQ_rk0 (by rw [h, map_zero])
  have hQ_gp4_ne : Q_gp4 ≠ 0 := by
    obtain ⟨f, hf⟩ := Countable.exists_injective_nat α
    refine fun h => hQgp4_moment (fun a => (f a : ℝ) + 1) ?_ (fun a => by positivity)
      (by rw [h, map_zero])
    exact fun a b hab => hf (by exact_mod_cast add_right_cancel hab)
  -- Step 4: an algebraically-independent-over-`ℚ` seed is a simultaneous non-root of both.
  obtain ⟨q_star, _, halg⟩ := exists_injective_algebraicIndependent_real (α × Fin 4)
  have hq_rk : eval q_star Q_rk ≠ 0 :=
    eval_ne_zero_of_coeffs_subset_range_of_algebraicIndependent halg hQ_rkrat hQ_rk_ne
  have hq_gp4 : eval q_star Q_gp4 ≠ 0 :=
    eval_ne_zero_of_coeffs_subset_range_of_algebraicIndependent halg hQgp4_rat hQ_gp4_ne
  -- The realization at the seed, its order-four general position, and the genuine-hinge condition.
  have hgp4 : (ofNormals (k := 2) G Q0.ends q_star).IsGeneralPosition4 := hQgp4_pred q_star hq_gp4
  have hgp2 : (ofNormals (k := 2) G Q0.ends q_star).IsGeneralPosition := hgp4.isGeneralPosition
  have hC : ∀ e u v, G.IsLink e u v →
      (ofNormals (k := 2) G Q0.ends q_star).toBodyHinge.supportExtensor e ≠ 0 := by
    intro e u v hl
    refine supportExtensor_ne_zero_of_isGeneralPosition
      (ofNormals (k := 2) G Q0.ends q_star) hgp2 ?_
    rw [ofNormals_ends]
    exact (hQ0ends e u v hl).ne
  -- Lower bound at `q*` (rank polynomial) and upper bound at `q*` (genuine-hinge deficiency bound).
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

end PanelHingeFramework

end CombinatorialRigidity.Molecular
