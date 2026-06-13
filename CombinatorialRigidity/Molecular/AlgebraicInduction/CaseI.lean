/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.AlgebraicInduction.GenericityDevice
import CombinatorialRigidity.Mathlib.RingTheory.MvPolynomial.Tower
import CombinatorialRigidity.Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.LinearAlgebra.Matrix.MvPolynomial

/-!
# The algebraic induction — Case I realization (`lem:case-I-realization`)

Phase 22a (molecular-conjecture program; see `notes/MolecularConjecture.md`). The Theorem-5.5
**Case I** (proper rigid subgraph) realization producer the genericity device feeds. On top of the
device (`AlgebraicInduction/GenericityDevice`), this file carries:

* the **shared-seed / block-triangular coupling** producers
  (`hasFullRankRealization_of_couple…`, `hasGenericFullRankRealization_of_couple…`,
  `…_blockTriangular_…`) — KT eq. 6.3 rank-addition over one common framework;
* the **exterior-column projection** `extProj` onto the surviving body columns;
* the Case-I composer `case_I_realization` (`lem:case-I-realization`), **green-modulo** a single
  dischargeable hypothesis = KT **Claim 6.4** (the red node `lem:claim-6-4`, deferred to Phase
  22b — the surviving block's exterior-projected rank at the generic placement);
* the `hglue` device-to-motive helpers and the `rankHypothesis_iff_pinnedMotionsOn` bridges.

See `ROADMAP.md` §22a / `notes/Phase22a.md` and the `sec:molecular-algebraic-induction` dep-graph
of `blueprint/src/chapter/algebraic-induction.tex`.
-/

namespace CombinatorialRigidity.Molecular

variable {k : ℕ}

open scoped Graph

variable {α β : Type*}

/-- **Case I shared-seed coupling: two rigid legs on the parent selector give a full-rank
realization** (`lem:case-I-splice-placement` / `lem:case-I-realization`, the simple Case-I
shared-seed coupling assembly N6b/N6c; Katoh–Tanigawa 2011 §6.2, eq. (6.6), the joint genericity of
the two Case-I legs; Phase 22). The genuine remaining content of the simple Case I, assembled from
the green leg-restricted rank polynomials and the general-position factor (G2): given the two
inductive legs `GH`, `Gc` (both subgraphs of `G`, sharing the contracted body `c` and covering
`V(G)`), each *infinitesimally rigid on its own vertex set* as a leg-native framework
`ofNormals GH ends q_H` resp.\ `ofNormals Gc ends q_c` at the **parent endpoint selector** `ends`
and at its **own** seed (`hrigH`/`hrigc`, the form the `ends`-swap brick
`infinitesimalMotions_ofNormals_eq_of_ends_swap` delivers from each leg's
`HasGenericFullRankRealization` inductive hypothesis), with transversal hinges at each leg's seed
(`hneH`/`hnec`), the parent graph `G` has a full-rank panel realization
`HasFullRankRealization k G`.

This is the witness-transfer the prior scaffolding reduced the Case I geometry to, now a pure
assembly of green bricks (the recon's `hends`-over-all-`β` obstruction was dissolved by the
leg-restricted chain): (i) each leg's rigidity yields its leg-restricted rank polynomial `Q_H`/`Q_c`
(`exists_rankPolynomial_of_rigidOn_linking`), nonzero at its own seed hence nonzero as a polynomial;
(ii) the general-position factor `Q_gp` (`exists_generalPosition_polynomial`) is nonzero (witnessed
at any moment-curve seed); (iii) the triple product `Q_H · Q_c · Q_gp` is a nonzero polynomial, so
`MvPolynomial.exists_eval_ne_zero` exhibits one shared seed `q₀` at which all three factors are
nonzero; (iv) at `q₀` each leg is rigid
(`isInfinitesimallyRigidOn_ofNormals_of_rankPolynomial_ne_zero_linking`,
consuming each leg's `hsupp`) and the parent normals are in general position (the `Q_gp` non-root);
(v) `hasFullRankRealization_of_splice_ofNormals` splices the two `q₀`-rigid legs along the shared
body into the parent realization, with general position discharging the splice's `hgp`.

The deliverable rank is concluded, not assumed (honesty gate): the inputs are the satisfiable
per-leg single-seed rigidities and per-seed transversalities (each a
`HasGenericFullRankRealization` leg, up
to the `ends`-swap), not the parent rank. The remaining red content of `lem:case-I-realization` is
the composer that supplies these leg hypotheses from the IH (the `ends`-swap step) and dispatches on
simplicity (non-simple → `hasFullRankRealization_of_splice_of_supportExtensor_ofNormals`, N6a;
simple → this lemma). -/
theorem PanelHingeFramework.hasFullRankRealization_of_couple_ofNormals [Finite α] [Finite β]
    (G : Graph α β) (ends : β → α × α)
    (hends : ∀ e, G.IsLink e (ends e).1 (ends e).2)
    (hne_ends : ∀ e, (ends e).1 ≠ (ends e).2) (hne : V(G).Nonempty)
    {GH Gc : Graph α β} (hGH : GH ≤ G) (hGc : Gc ≤ G)
    {c : α} (hcH : c ∈ V(GH)) (hcc : c ∈ V(Gc)) (hcover : V(G) ⊆ V(GH) ∪ V(Gc))
    (hnevH : V(GH).Nonempty) (hnevc : V(Gc).Nonempty)
    {qH qc : α × Fin (k + 2) → ℝ}
    (hneH : ∀ e, GH.IsLink e (ends e).1 (ends e).2 →
      (PanelHingeFramework.ofNormals GH ends qH).toBodyHinge.supportExtensor e ≠ 0)
    (hnec : ∀ e, Gc.IsLink e (ends e).1 (ends e).2 →
      (PanelHingeFramework.ofNormals Gc ends qc).toBodyHinge.supportExtensor e ≠ 0)
    (hrigH :
      (PanelHingeFramework.ofNormals GH ends qH).toBodyHinge.IsInfinitesimallyRigidOn V(GH))
    (hrigc :
      (PanelHingeFramework.ofNormals Gc ends qc).toBodyHinge.IsInfinitesimallyRigidOn V(Gc)) :
    PanelHingeFramework.HasFullRankRealization k G := by
  classical
  -- A leg's linking edge `e` (`GH.IsLink e u v`) links the parent selector *within the leg*: `e` is
  -- in `E(GH)` and links `ends` in `G` (`hends`), so by `IsSubgraph.isLink_iff` it links in `GH`.
  have hendsH : ∀ e u v, GH.IsLink e u v → GH.IsLink e (ends e).1 (ends e).2 := fun e _ _ h =>
    (Graph.IsSubgraph.isLink_iff hGH h.edge_mem).mpr (hends e)
  have hendsc : ∀ e u v, Gc.IsLink e u v → Gc.IsLink e (ends e).1 (ends e).2 := fun e _ _ h =>
    (Graph.IsSubgraph.isLink_iff hGc h.edge_mem).mpr (hends e)
  -- (i) Each leg's leg-restricted rank polynomial: a `panelRow`-index subset `s` of full size and a
  -- `MvPolynomial` `Q` nonzero at the leg's own seed whose every non-root gives the subfamily LI.
  obtain ⟨sH, QH, hsuppH, hcardH, hQ0H, _, hLIH⟩ :=
    PanelHingeFramework.exists_rankPolynomial_of_rigidOn_linking GH ends hendsH hneH hnevH hrigH
  obtain ⟨sc, Qc, hsuppc, hcardc, hQ0c, _, hLIc⟩ :=
    PanelHingeFramework.exists_rankPolynomial_of_rigidOn_linking Gc ends hendsc hnec hnevc hrigc
  -- (ii) The general-position factor: nonzero (witnessed at a moment-curve seed), non-roots general
  -- position.
  obtain ⟨Qgp, hQgp_ne, _, hQgp_pos⟩ :=
    exists_generalPosition_polynomial (k := k) G ends
  -- (iii) The triple product is a nonzero polynomial (each factor nonzero), so it has a non-root.
  have hQHne : QH ≠ 0 := fun h => hQ0H (by rw [h, map_zero])
  have hQcne : Qc ≠ 0 := fun h => hQ0c (by rw [h, map_zero])
  have hQgpne : Qgp ≠ 0 := by
    obtain ⟨f, hf⟩ := Countable.exists_injective_nat α
    refine fun h => hQgp_ne (fun a => (f a : ℝ)) ?_ (by rw [h, map_zero])
    exact fun a b hab => hf (Nat.cast_injective hab)
  obtain ⟨q₀, hq₀⟩ := MvPolynomial.exists_eval_ne_zero
    (mul_ne_zero (mul_ne_zero hQHne hQcne) hQgpne)
  rw [map_mul, map_mul] at hq₀
  have hq₀H : MvPolynomial.eval q₀ QH ≠ 0 := fun h => hq₀ (by rw [h]; ring)
  have hq₀c : MvPolynomial.eval q₀ Qc ≠ 0 := fun h => hq₀ (by rw [h]; ring)
  have hq₀gp : MvPolynomial.eval q₀ Qgp ≠ 0 := fun h => hq₀ (by rw [h]; ring)
  -- (iv) At `q₀` each leg is rigid (consuming its `hsupp`), and the parent normals are general.
  have hrigH₀ : (PanelHingeFramework.ofNormals GH ends q₀).toBodyHinge.IsInfinitesimallyRigidOn
      V(GH) :=
    PanelHingeFramework.isInfinitesimallyRigidOn_ofNormals_of_rankPolynomial_ne_zero_linking
      GH ends hnevH hsuppH hcardH hLIH hq₀H
  have hrigc₀ : (PanelHingeFramework.ofNormals Gc ends q₀).toBodyHinge.IsInfinitesimallyRigidOn
      V(Gc) :=
    PanelHingeFramework.isInfinitesimallyRigidOn_ofNormals_of_rankPolynomial_ne_zero_linking
      Gc ends hnevc hsuppc hcardc hLIc hq₀c
  have hgp : (PanelHingeFramework.ofNormals (k := k) G ends q₀).IsGeneralPosition :=
    hQgp_pos q₀ hq₀gp
  -- (v) Splice the two `q₀`-rigid legs along the shared body into the parent realization.
  exact PanelHingeFramework.hasFullRankRealization_of_splice_ofNormals G ends hends hne_ends hne
    hgp hGH hGc hcH hcc hcover hrigH₀ hrigc₀

/-- **Case I shared-seed coupling, *generic* form: two rigid legs on the parent selector give a
*general-position* full-rank realization** (`lem:case-I-realization`, the simple Case-I coupling at
the strengthened motive, G2c; Katoh–Tanigawa 2011 §6.2, eq. (6.6); Phase 22a). The generic sibling
of `hasFullRankRealization_of_couple_ofNormals`: from the *same* per-leg inputs — each leg
`GH`, `Gc` infinitesimally rigid as a leg-native framework `ofNormals · ends ·` at its **own** seed
and at the **parent** endpoint selector `ends`, with transversal hinges — it concludes the
strengthened motive `HasGenericFullRankRealization k G` rather than the bare
`HasFullRankRealization k G`.

The proof is identical up to the final splice. Steps (i)–(iv) (each leg's leg-restricted rank
polynomial × the general-position factor (G2) → a shared non-root `q₀` at which both legs are rigid
*and* the parent normals are general position) are the same as the bare coupling, so this lemma
shares the witness-transfer. Only step (v) differs: where the bare coupling splices the two
`q₀`-rigid legs through the device-routing `hasFullRankRealization_of_splice_ofNormals` (which loses
the general position of `q₀` on the way through the genericity device and so can only conclude the
bare motive), the generic coupling splices through the genericity-device-free
`hasGenericFullRankRealization_of_splice_ofNormals` (N6-G1), which realizes at the GP seed `q₀`
*itself* and so keeps both the rigidity (from the block-triangular glue) and the general position
(`hgp`). This is the producer the simple Case I (KT Lemma 6.3/6.5) consumes to discharge
`theorem_55_generic`'s `hcontractGP` GP conjunct: the composer (N6-G3 / G2c) supplies the two leg
rigidities from the conditioned IH (transported to the parent selector by
`hasGenericRealization_transport_ends`) and this lemma lands the `G.Simple → GP G` conjunct of
`theorem_55_generic`'s motive. -/
theorem PanelHingeFramework.hasGenericFullRankRealization_of_couple_ofNormals [Finite α] [Finite β]
    (G : Graph α β) (ends : β → α × α)
    (hends : ∀ e, G.IsLink e (ends e).1 (ends e).2)
    {GH Gc : Graph α β} (hGH : GH ≤ G) (hGc : Gc ≤ G)
    {c : α} (hcH : c ∈ V(GH)) (hcc : c ∈ V(Gc)) (hcover : V(G) ⊆ V(GH) ∪ V(Gc))
    (hnevH : V(GH).Nonempty) (hnevc : V(Gc).Nonempty)
    {qH qc : α × Fin (k + 2) → ℝ}
    (hneH : ∀ e, GH.IsLink e (ends e).1 (ends e).2 →
      (PanelHingeFramework.ofNormals GH ends qH).toBodyHinge.supportExtensor e ≠ 0)
    (hnec : ∀ e, Gc.IsLink e (ends e).1 (ends e).2 →
      (PanelHingeFramework.ofNormals Gc ends qc).toBodyHinge.supportExtensor e ≠ 0)
    (hrigH :
      (PanelHingeFramework.ofNormals GH ends qH).toBodyHinge.IsInfinitesimallyRigidOn V(GH))
    (hrigc :
      (PanelHingeFramework.ofNormals Gc ends qc).toBodyHinge.IsInfinitesimallyRigidOn V(Gc))
    (n : ℕ) (hne : V(G).Nonempty) (hdef : G.deficiency n = 0) :
    PanelHingeFramework.HasGenericFullRankRealization k n G := by
  classical
  -- Steps (i)–(iv): both leg rank polynomials and the general-position factor are *rational*
  -- (`Q.coeffs ⊆ range (algebraMap ℚ ℝ)`), so the algebraically-independent-over-`ℚ` seed `q₀`
  -- (`exists_injective_algebraicIndependent_real`) is a simultaneous non-root of all three — both
  -- legs are rigid at `q₀`, the parent normals are in general position, *and* `q₀` carries the
  -- motive's algebraic-independence conjunct.
  have hendsH : ∀ e u v, GH.IsLink e u v → GH.IsLink e (ends e).1 (ends e).2 := fun e _ _ h =>
    (Graph.IsSubgraph.isLink_iff hGH h.edge_mem).mpr (hends e)
  have hendsc : ∀ e u v, Gc.IsLink e u v → Gc.IsLink e (ends e).1 (ends e).2 := fun e _ _ h =>
    (Graph.IsSubgraph.isLink_iff hGc h.edge_mem).mpr (hends e)
  obtain ⟨sH, QH, hsuppH, hcardH, hQ0H, hQHrat, hLIH⟩ :=
    PanelHingeFramework.exists_rankPolynomial_of_rigidOn_linking GH ends hendsH hneH hnevH hrigH
  obtain ⟨sc, Qc, hsuppc, hcardc, hQ0c, hQcrat, hLIc⟩ :=
    PanelHingeFramework.exists_rankPolynomial_of_rigidOn_linking Gc ends hendsc hnec hnevc hrigc
  obtain ⟨Qgp, hQgp_ne, hQgprat, hQgp_pos⟩ :=
    exists_generalPosition_polynomial (k := k) G ends
  have hQHne : QH ≠ 0 := fun h => hQ0H (by rw [h, map_zero])
  have hQcne : Qc ≠ 0 := fun h => hQ0c (by rw [h, map_zero])
  have hQgpne : Qgp ≠ 0 := by
    obtain ⟨f, hf⟩ := Countable.exists_injective_nat α
    refine fun h => hQgp_ne (fun a => (f a : ℝ)) ?_ (by rw [h, map_zero])
    exact fun a b hab => hf (Nat.cast_injective hab)
  obtain ⟨q₀, _, halg⟩ := exists_injective_algebraicIndependent_real (α × Fin (k + 2))
  have hq₀H : MvPolynomial.eval q₀ QH ≠ 0 :=
    MvPolynomial.eval_ne_zero_of_coeffs_subset_range_of_algebraicIndependent halg hQHrat hQHne
  have hq₀c : MvPolynomial.eval q₀ Qc ≠ 0 :=
    MvPolynomial.eval_ne_zero_of_coeffs_subset_range_of_algebraicIndependent halg hQcrat hQcne
  have hq₀gp : MvPolynomial.eval q₀ Qgp ≠ 0 :=
    MvPolynomial.eval_ne_zero_of_coeffs_subset_range_of_algebraicIndependent halg hQgprat hQgpne
  have hrigH₀ : (PanelHingeFramework.ofNormals GH ends q₀).toBodyHinge.IsInfinitesimallyRigidOn
      V(GH) :=
    PanelHingeFramework.isInfinitesimallyRigidOn_ofNormals_of_rankPolynomial_ne_zero_linking
      GH ends hnevH hsuppH hcardH hLIH hq₀H
  have hrigc₀ : (PanelHingeFramework.ofNormals Gc ends q₀).toBodyHinge.IsInfinitesimallyRigidOn
      V(Gc) :=
    PanelHingeFramework.isInfinitesimallyRigidOn_ofNormals_of_rankPolynomial_ne_zero_linking
      Gc ends hnevc hsuppc hcardc hLIc hq₀c
  have hgp : (PanelHingeFramework.ofNormals (k := k) G ends q₀).IsGeneralPosition :=
    hQgp_pos q₀ hq₀gp
  -- (v') The generic splice: realize at the alg-indep GP seed `q₀` itself (bypassing the device),
  -- so general position survives and the conclusion is the strengthened generic motive. The all-`β`
  -- `hends` weakens to the edge-restricted link-recording form the splice producer needs.
  exact PanelHingeFramework.hasGenericFullRankRealization_of_splice_ofNormals G ends
    (fun e _ _ _ => hends e) hgp halg hGH hGc hcH hcc hcover hrigH₀ hrigc₀ n hne hdef

/-- **Case I shared-seed coupling, *body-set* form: two legs rigid on per-leg body sets `sH`/`sc`
give a full-rank realization** (`lem:case-I-realization`, the body-set coupling N6-G3-G3c-ii;
Katoh–Tanigawa 2011 §6.2, eqs. (6.3), (6.6), Phase 22a). The body-set generalization of
`hasFullRankRealization_of_couple_ofNormals`: where the all-of-`V(·)` coupling demands each leg
rigid on its full vertex set `V(GH)`/`V(Gc)`, this threads per-leg body sets `sH`/`sc`
(`c ∈ sH ∩ sc`, `V(G) ⊆ sH ∪ sc`), the form Case I's *contraction* leg `Gc = G ＼ E(H)` forces — it
is rigid only on
the surviving bodies `sc = (V(G)∖V(H)) ∪ {r}` (KT eq. (6.3)'s `V∖V′`), not all of `V(Gc) = V(G)`.

The witness-transfer is the same five steps, lifted to the body-set bricks (design doc §1.9): (i)
each leg's *body-set* leg-restricted rank polynomial `Q_H`/`Q_c`
(`exists_rankPolynomial_of_rigidOn_linking_set`), nonzero at its own seed; (ii) the general-position
factor `Q_gp`; (iii) the triple product has a shared non-root `q₀`; (iv) at `q₀` each leg is rigid
*on its body set* (`isInfinitesimallyRigidOn_ofNormals_of_rankPolynomial_ne_zero_linking_set`, the
body-set consumer — this is the only step that genuinely changes, since the body-set N3 needs the
**complement-isolation equality** `hpinH`/`hpinc` `finrank (pinnedMotionsOn s) = D·|sᶜ|`, false off
`V(G)` from the count alone) and the parent normals are in general position; (v) the body-set splice
producer `hasFullRankRealization_of_splice_set_of_supportExtensor` glues the two body-set-rigid legs
along the shared body into the parent's rigidity on `V(G) ⊆ sH ∪ sc` and lands the full-rank
realization.

The complement-isolation hypotheses `hpinH`/`hpinc` are quantified over all normal assignments
(`∀ q, finrank (pinnedMotionsOn s) = D·|sᶜ|`) because the shared seed `q₀` is unknown at call time:
the body-set pin dimension is graph-structural (which projection kernels the surviving edges leave
free), so it is constant across normals, making this the honest leg-specific isolation fact. It is
discharged per-leg by the composer (G3c-iii): `sH := V(H)` makes `hpinH` the green
`finrank_pinnedMotionsOn_vertexSet`, and the contraction leg's interior bodies are isolated in
`G ＼ E(H)`. The deliverable rank is concluded, not assumed. -/
theorem PanelHingeFramework.hasFullRankRealization_of_couple_ofNormals_set [Finite α] [Finite β]
    (G : Graph α β) (ends : β → α × α)
    (hends : ∀ e, G.IsLink e (ends e).1 (ends e).2)
    (hne_ends : ∀ e, (ends e).1 ≠ (ends e).2) (hne : V(G).Nonempty)
    {GH Gc : Graph α β} (hGH : GH ≤ G) (hGc : Gc ≤ G)
    {sH sc : Set α} {c : α} (hcH : c ∈ sH) (hcc : c ∈ sc) (hcover : V(G) ⊆ sH ∪ sc)
    (hnesH : sH.Nonempty) (hnesc : sc.Nonempty)
    {qH qc : α × Fin (k + 2) → ℝ}
    (hpinH : ∀ q : α × Fin (k + 2) → ℝ, Module.finrank ℝ
      ((PanelHingeFramework.ofNormals GH ends q).toBodyHinge.pinnedMotionsOn sH)
      = screwDim k * sHᶜ.ncard)
    (hpinc : ∀ q : α × Fin (k + 2) → ℝ, Module.finrank ℝ
      ((PanelHingeFramework.ofNormals Gc ends q).toBodyHinge.pinnedMotionsOn sc)
      = screwDim k * scᶜ.ncard)
    (hneH : ∀ e, GH.IsLink e (ends e).1 (ends e).2 →
      (PanelHingeFramework.ofNormals GH ends qH).toBodyHinge.supportExtensor e ≠ 0)
    (hnec : ∀ e, Gc.IsLink e (ends e).1 (ends e).2 →
      (PanelHingeFramework.ofNormals Gc ends qc).toBodyHinge.supportExtensor e ≠ 0)
    (hrigH :
      (PanelHingeFramework.ofNormals GH ends qH).toBodyHinge.IsInfinitesimallyRigidOn sH)
    (hrigc :
      (PanelHingeFramework.ofNormals Gc ends qc).toBodyHinge.IsInfinitesimallyRigidOn sc) :
    PanelHingeFramework.HasFullRankRealization k G := by
  classical
  have hendsH : ∀ e u v, GH.IsLink e u v → GH.IsLink e (ends e).1 (ends e).2 := fun e _ _ h =>
    (Graph.IsSubgraph.isLink_iff hGH h.edge_mem).mpr (hends e)
  have hendsc : ∀ e u v, Gc.IsLink e u v → Gc.IsLink e (ends e).1 (ends e).2 := fun e _ _ h =>
    (Graph.IsSubgraph.isLink_iff hGc h.edge_mem).mpr (hends e)
  -- (i) Each leg's *body-set* leg-restricted rank polynomial at its own seed.
  obtain ⟨rsH, QH, hsuppH, hcardH, hQ0H, _, hLIH⟩ :=
    PanelHingeFramework.exists_rankPolynomial_of_rigidOn_linking_set GH ends hendsH hneH hnesH hrigH
  obtain ⟨rsc, Qc, hsuppc, hcardc, hQ0c, _, hLIc⟩ :=
    PanelHingeFramework.exists_rankPolynomial_of_rigidOn_linking_set Gc ends hendsc hnec hnesc hrigc
  -- (ii) The general-position factor.
  obtain ⟨Qgp, hQgp_ne, _, hQgp_pos⟩ :=
    exists_generalPosition_polynomial (k := k) G ends
  -- (iii) The triple product has a shared non-root `q₀`.
  have hQHne : QH ≠ 0 := fun h => hQ0H (by rw [h, map_zero])
  have hQcne : Qc ≠ 0 := fun h => hQ0c (by rw [h, map_zero])
  have hQgpne : Qgp ≠ 0 := by
    obtain ⟨f, hf⟩ := Countable.exists_injective_nat α
    refine fun h => hQgp_ne (fun a => (f a : ℝ)) ?_ (by rw [h, map_zero])
    exact fun a b hab => hf (Nat.cast_injective hab)
  obtain ⟨q₀, hq₀⟩ := MvPolynomial.exists_eval_ne_zero
    (mul_ne_zero (mul_ne_zero hQHne hQcne) hQgpne)
  rw [map_mul, map_mul] at hq₀
  have hq₀H : MvPolynomial.eval q₀ QH ≠ 0 := fun h => hq₀ (by rw [h]; ring)
  have hq₀c : MvPolynomial.eval q₀ Qc ≠ 0 := fun h => hq₀ (by rw [h]; ring)
  have hq₀gp : MvPolynomial.eval q₀ Qgp ≠ 0 := fun h => hq₀ (by rw [h]; ring)
  -- (iv) At `q₀` each leg is rigid *on its body set* (body-set consumer, carrying the leg's
  -- complement-isolation equality `hpinH`/`hpinc`), and the parent normals are general.
  have hrigH₀ :
      (PanelHingeFramework.ofNormals GH ends q₀).toBodyHinge.IsInfinitesimallyRigidOn sH :=
    PanelHingeFramework.isInfinitesimallyRigidOn_ofNormals_of_rankPolynomial_ne_zero_linking_set
      GH ends hnesH (hpinH q₀) hsuppH hcardH hLIH hq₀H
  have hrigc₀ :
      (PanelHingeFramework.ofNormals Gc ends q₀).toBodyHinge.IsInfinitesimallyRigidOn sc :=
    PanelHingeFramework.isInfinitesimallyRigidOn_ofNormals_of_rankPolynomial_ne_zero_linking_set
      Gc ends hnesc (hpinc q₀) hsuppc hcardc hLIc hq₀c
  have hgp : (PanelHingeFramework.ofNormals (k := k) G ends q₀).IsGeneralPosition :=
    hQgp_pos q₀ hq₀gp
  -- (v) The body-set splice glues the two body-set-rigid legs into the parent realization, with
  -- general position discharging every hinge's transversality.
  exact PanelHingeFramework.hasFullRankRealization_of_splice_set_of_supportExtensor G ends hends hne
    (fun e => (PanelHingeFramework.ofNormals G ends q₀).supportExtensor_ne_zero_of_isGeneralPosition
      hgp (by simpa using hne_ends e))
    hGH hGc hcH hcc hcover hrigH₀ hrigc₀

/-- **The canonical-`endsOf` panel realization records its own graph's links** (`thm:theorem-55`,
the motive's link-recording conjunct; Katoh–Tanigawa 2011 §6.2, Phase 22b route (i)). For the
canonical endpoint selector `G.endsOf`, the free-normal panel framework `ofNormals G G.endsOf q₀`
records every link of `G` up to swap: if `G.IsLink e u v` then its selector
`(ofNormals G G.endsOf q₀).ends e = G.endsOf e` is `(u, v)` or its swap `(v, u)`.

This is the **link-recording conjunct** the strengthened generic motive
`HasGenericFullRankRealization` carries (Phase 22b route (i), design doc §1.24 Commit 2): it is the
guarantee that the realizing framework's endpoint selector pins, for each link, the same unordered
pair the link does — exactly what the `ends`-swap transport
(`hasGenericRealization_transport_ends`'s `hswap`) and the contraction-leg alignment of Case I's
composer consume. Every fresh producer builds `ofNormals G G.endsOf q₀` (the composer manufactures
the canonical `endsOf` selector, `isLink_endsOf`), so this lemma is the term each one hands the
strengthened motive. The content is `Graph.endsOf_eq_or_swap` (the canonical selector orients along
any given link, up to order, via mathlib's `IsLink.eq_and_eq_or_eq_and_eq`) read componentwise
through `ofNormals_ends`. -/
theorem PanelHingeFramework.ofNormals_endsOf_recordsLinks [Inhabited α]
    (G : Graph α β) (q₀ : α × Fin (k + 2) → ℝ) :
    ∀ e u v, G.IsLink e u v →
      (((PanelHingeFramework.ofNormals G G.endsOf q₀).ends e).1 = u ∧
        ((PanelHingeFramework.ofNormals G G.endsOf q₀).ends e).2 = v) ∨
      (((PanelHingeFramework.ofNormals G G.endsOf q₀).ends e).1 = v ∧
        ((PanelHingeFramework.ofNormals G G.endsOf q₀).ends e).2 = u) := by
  intro e u v he
  rw [PanelHingeFramework.ofNormals_ends]
  rcases G.endsOf_eq_or_swap he with h | h
  · exact Or.inl ⟨by rw [h], by rw [h]⟩
  · exact Or.inr ⟨by rw [h], by rw [h]⟩

/-- **A link-recording selector agrees up to swap with the canonical parent selector on a subgraph's
links** (`lem:case-I-realization` infra, the `H`-leg alignment discharge; Katoh–Tanigawa 2011 §6.2,
Phase 22b route (i), design doc §1.24 item 4, Commit 4a). If an endpoint selector `ends'` records
every link of a subgraph `H ≤ G` up to swap (the link-recording conjunct of the strengthened motive
`HasGenericFullRankRealization`, e.g. an inductive leg realization's `Q.ends`), then on every link
of `H` it agrees, up to swap, with the canonical parent selector `G.endsOf`.

This is the discharge of the `H`-leg `hswap` the Case-I composer previously carried as a `hbundle`
hypothesis: an `H`-link `e u v` is also a `G`-link (`H ≤ G`, `IsLink.of_le`), so both selectors
pin the *same* unordered pair — `ends'` by `hrec`, `G.endsOf` by `endsOf_eq_or_swap` — hence they
agree up to order. The four cases of the two disjunctions collapse pairwise into the swap
disjunction. This is precisely the "two link-recording selectors agree up to swap" reasoning the
motive strengthening (route (i)) was designed to enable, now that the leg's IH realization carries
link-recording. -/
theorem PanelHingeFramework.recordsLinks_swap_endsOf [Inhabited α]
    {G H : Graph α β} (hle : H ≤ G) (ends' : β → α × α)
    (hrec : ∀ e u v, H.IsLink e u v →
      ((ends' e).1 = u ∧ (ends' e).2 = v) ∨ ((ends' e).1 = v ∧ (ends' e).2 = u)) :
    ∀ e u v, H.IsLink e u v →
      ((ends' e).1 = (G.endsOf e).1 ∧ (ends' e).2 = (G.endsOf e).2) ∨
      ((ends' e).1 = (G.endsOf e).2 ∧ (ends' e).2 = (G.endsOf e).1) := by
  intro e u v he
  rcases G.endsOf_eq_or_swap (he.of_le hle) with hG | hG <;>
    rcases hrec e u v he with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    simp only [hG] <;>
    [exact Or.inl ⟨h1, h2⟩; exact Or.inr ⟨h1, h2⟩;
     exact Or.inr ⟨h1, h2⟩; exact Or.inl ⟨h1, h2⟩]

/-- **Swapping a hinge's two endpoints leaves the panel framework's motion space unchanged**
(`lem:case-I-splice-placement` infra, the `ends`-selector independence of leg rigidity;
Katoh–Tanigawa 2011 §6.2, Phase 22). For two endpoint selectors `ends`, `ends'` that record the
*same* unordered link of every edge of `G` (each `ends' e` is `ends e` or its swap, `hswap`), the
free-normal panel frameworks `ofNormals G ends q` and `ofNormals G ends' q` on the *same* normal
assignment `q` have the same null space (`infinitesimalMotions` of the two `toBodyHinge`
interpretations agree).

The motion space depends on the endpoint selector only through the support extensors of the
*linking* edges (`infinitesimalMotions_eq_of_isLink_supportExtensor`), and the support extensor
`panelSupportExtensor (q u) (q v) = complementIso (normalsJoin (q u) (q v))` is *anti-symmetric* in
its two normals (`panelSupportExtensor_swap`: `normalsJoin` is the alternating `ιMulti ℝ 2 ![·,·]`,
so swapping the endpoints negates it). The hinge constraint is membership in
`span {supportExtensor e}`, which is unchanged by negation, so swapping an edge's two endpoints
leaves every hinge constraint — hence the whole motion space — fixed.

This is the first decomposable brick of the Case-I shared-seed coupling
(`lem:case-I-splice-placement`, red): it re-expresses one inductive leg's rigidity at its *own*
endpoint selector `ends_H` (the form its `HasGenericFullRankRealization` IH supplies) at the
*parent's* endpoint selector `ends` (the form the splice
`hasFullRankRealization_of_splice_ofNormals` consumes). For an edge of the leg, `ends_H e` and
`ends e` record the same `IsLink`, hence agree up
to swap (`IsLink.left_eq_or_eq`), so the leg's rigidity is the same at both selectors — the
recon-surfaced `ends`-alignment obstruction, dissolved on the *linking* edges. -/
theorem PanelHingeFramework.infinitesimalMotions_ofNormals_eq_of_ends_swap
    (G : Graph α β) (ends ends' : β → α × α) (q : α × Fin (k + 2) → ℝ)
    (hswap : ∀ e u v, G.IsLink e u v →
      ((ends' e).1 = (ends e).1 ∧ (ends' e).2 = (ends e).2) ∨
      ((ends' e).1 = (ends e).2 ∧ (ends' e).2 = (ends e).1)) :
    (PanelHingeFramework.ofNormals G ends q).toBodyHinge.infinitesimalMotions =
      (PanelHingeFramework.ofNormals G ends' q).toBodyHinge.infinitesimalMotions := by
  refine BodyHingeFramework.infinitesimalMotions_eq_of_isLink_span_supportExtensor _ _ rfl ?_
  intro e u v he
  -- The two support extensors agree up to a sign (anti-symmetry of `panelSupportExtensor`), so
  -- their spans (the lines the hinge constraints reference) coincide.
  simp only [PanelHingeFramework.toBodyHinge_supportExtensor,
    PanelHingeFramework.ofNormals_normal, PanelHingeFramework.ofNormals_ends]
  rcases hswap e u v he with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
  · rw [h1, h2, panelSupportExtensor_swap, ← Set.neg_singleton, Submodule.span_neg]

/-- **A leg's general-position rigid IH realization transports to the parent endpoint selector**
(`lem:case-I-realization` infra, the N6-composer `ends`-swap step; Katoh–Tanigawa 2011 §6.2, Phase
22). The genuine first decomposable piece of the Case-I composer: it bridges one inductive leg's
`HasGenericFullRankRealization` (a *general-position* panel-hinge framework `Q` on the leg `GH`,
infinitesimally rigid on `V(GH)`, recorded at the leg's *own* endpoint selector `Q.ends`) to the
shape the shared-seed coupling `hasFullRankRealization_of_couple_ofNormals` consumes: a free-normal
`ofNormals GH ends qH` at the **parent** selector `ends`, both *transversal at `ends`* (`hneH`) and
*rigid on `V(GH)`* (`hrigH`).

The two re-expressions are the brick's content. (1) **Selector transport.** `Q` is *literally* its
own free-normal form `ofNormals GH Q.ends qH` with `qH p := Q.normal p.1 p.2` (`rfl` after
`Q.graph = GH`); the `ends`-swap brick `infinitesimalMotions_ofNormals_eq_of_ends_swap` then carries
its rigidity from `Q.ends` to the parent `ends`, since the two selectors record the same unordered
link of every edge of `GH` (`hswap` — supplied by the composer from `GH ≤ G`: a leg edge's link is
recorded by both selectors, so they agree up to swap). Rigidity-on-`V(GH)` is invariant under the
`infinitesimalMotions` equality because `IsInfinitesimallyRigidOn` quantifies over
`IsInfinitesimalMotion = (· ∈ infinitesimalMotions)`. (2) **Transversality at `ends`.** General
position is a property of the normals `qH` alone (`ofNormals_normal`), unchanged by the selector, so
`ofNormals GH ends qH` is again in general position; for any *linking* edge whose `ends`-endpoints
are distinct (`hne_ends`, restricted to links — the all-`β` form is unsatisfiable for the canonical
`endsOf` selector, which returns junk on non-edges; see `endsOf_fst_ne_snd`),
`supportExtensor_ne_zero_of_isGeneralPosition` gives the transversal hinge `hneH`.

This is the composer's per-leg adapter; the composer itself (`lem:case-I-realization`) supplies
`hswap` from the leg-subgraph relation, applies this brick to each of the two legs (the rigid block
`H` and the contraction `G/E(H)`), and feeds the two outputs to
`hasFullRankRealization_of_couple_ofNormals`. -/
theorem PanelHingeFramework.hasGenericRealization_transport_ends
    (GH : Graph α β) (ends : β → α × α) (Q : PanelHingeFramework k α β)
    (hQg : Q.graph = GH) (hQgp : Q.IsGeneralPosition)
    (hQrig : Q.toBodyHinge.IsInfinitesimallyRigidOn V(GH))
    (hswap : ∀ e u v, GH.IsLink e u v →
      ((Q.ends e).1 = (ends e).1 ∧ (Q.ends e).2 = (ends e).2) ∨
      ((Q.ends e).1 = (ends e).2 ∧ (Q.ends e).2 = (ends e).1))
    (hne_ends : ∀ e, GH.IsLink e (ends e).1 (ends e).2 → (ends e).1 ≠ (ends e).2) :
    ∃ qH : α × Fin (k + 2) → ℝ,
      (∀ e, GH.IsLink e (ends e).1 (ends e).2 →
        (PanelHingeFramework.ofNormals GH ends qH).toBodyHinge.supportExtensor e ≠ 0) ∧
      (PanelHingeFramework.ofNormals GH ends qH).toBodyHinge.IsInfinitesimallyRigidOn V(GH) := by
  subst hQg
  set qH := (fun p => Q.normal p.1 p.2 : α × Fin (k + 2) → ℝ) with hqH
  -- General position transfers to `ofNormals … ends …` verbatim (normals are unchanged).
  have hgp' : (PanelHingeFramework.ofNormals Q.graph ends qH).IsGeneralPosition := by
    intro a b hab
    simpa only [hqH, PanelHingeFramework.ofNormals_normal] using hQgp a b hab
  -- The swap brick equates the motion spaces of `Q = ofNormals … Q.ends …` and `ofNormals … ends`.
  have hmot : (PanelHingeFramework.ofNormals Q.graph ends qH).toBodyHinge.infinitesimalMotions
      = (PanelHingeFramework.ofNormals Q.graph Q.ends qH).toBodyHinge.infinitesimalMotions :=
    PanelHingeFramework.infinitesimalMotions_ofNormals_eq_of_ends_swap Q.graph ends Q.ends qH hswap
  refine ⟨qH, fun e he =>
    (PanelHingeFramework.ofNormals Q.graph ends qH).supportExtensor_ne_zero_of_isGeneralPosition
      hgp' (by rw [PanelHingeFramework.ofNormals_ends]; exact hne_ends e he), ?_⟩
  -- Rigidity at `ends`: `IsInfinitesimallyRigidOn` quantifies over `· ∈ infinitesimalMotions`.
  intro S hS u hu v hv
  refine hQrig S ?_ u hu v hv
  rw [← BodyHingeFramework.mem_infinitesimalMotions] at hS ⊢
  rw [hmot] at hS
  exact hS

/-- **The Case-I contraction leg's rigidity transports across the collapse map to the
surviving-edge subgraph `G ＼ E(H)`** (`lem:case-I-realization` infra, the N6-G3-G3a Claim-6.4
collapse transport; Katoh–Tanigawa 2011 §6.2, eqs. (6.3), (6.7), (6.9), Phase 22a).

The second leg the Case-I splice consumes. KT's eq. (6.3) block decomposition of `R(G,p)` has the
rigid block `H` in one block and the parent **restricted to the surviving edges**
`R(G,p; E∖E′, V∖V′)` in the other — and the surviving-edge subgraph is `G.deleteEdges E(H)`
(`edgeSet_rigidContract` reads `E(G/E(H)) = E(G) ∖ E(H)`), a *literal* `≤ G` subgraph, **not** the
relabelled `G.rigidContract H r` (which collapses `V(H) ↦ r` and so is not comparable to `G`; no
`rigidContract_le` exists or can). So the contraction leg of the splice coupling is `G ＼ E(H)`, and
the collapse to the representative body `v∗ = r` lives entirely on the *placement* side (eq. (6.7)'s
`p_{E∖E′}`).

The genuinely-new analytic content this brick performs is **KT Claim 6.4** (eq. (6.9)): the
contraction's inductive realization is a general-position rigid realization of the *abstract
relabelled* graph `G.rigidContract H r` (the `HasGenericFullRankRealization` IH, `hQ`), and Claim
6.4 transports its rank across the collapse map — because the joint panel coefficients are
algebraically independent over ℚ (general position), the surviving-edge `p_{E∖E′}`-realization of
`G ＼ E(H)` attains the contraction's rank. In the project's `V(G)`-relative rank language this is
exactly: there is a seed `q_c` at which `(ofNormals (G.deleteEdges E(H)) ends q_c)` is
infinitesimally rigid on the contraction's body set `(V(G) ∖ V(H)) ∪ {r}`. **This rank-attainment
across the relabel is the last research-shaped Case-I brick** — no green brick converts a
relabelled-graph rigidity into the original-endpoint rigidity, because the collapse map
`collapseTo r V(H)` redirects each surviving edge's endpoints (hence which panel normals its support
extensor uses), and recovering the rank at the *un-collapsed* endpoints is precisely the
algebraic-independence statement of Claim 6.4. It is therefore carried here as the explicit
hypothesis `htransport`, in the established Phase-21b green-modulo `h…` idiom (exactly as Cases I/II
carried the genericity device before Phase 21b): `lem:case-III` / `thm:theorem-55` stay red, but
every step this brick *discharges* is honest, and the obligation is tracked as a single visible
hypothesis pinned to KT Claim 6.4 rather than buried in a `sorry` or an `axiom`.

Given `htransport`, the brick is a thin repackaging: it forwards the seed `q_c` and the
surviving-edge rigidity, both at the **parent** endpoint selector `ends` (the form the G2c coupling
`hasGenericFullRankRealization_of_couple_ofNormals` consumes for its `Gc := G.deleteEdges E(H)`
leg). The body set `(V(G) ∖ V(H)) ∪ {r}` is `V(G.rigidContract H r)`
(`rigidContract_vertexSet_ncard`'s set form), the set on which the contraction's rank is the
relevant `V(G)`-relative count; the coupling reads it as `V(G.deleteEdges E(H)) = V(G) ⊇` the
cover. -/
theorem PanelHingeFramework.rigidContract_rigidity_transport [Finite α]
    (G H : Graph α β) (ends : β → α × α) {r : α}
    (n : ℕ) (hne : V(G.rigidContract H r).Nonempty) (hdef : (G.rigidContract H r).deficiency n = 0)
    (hQ : PanelHingeFramework.HasGenericFullRankRealization k n (G.rigidContract H r))
    (htransport : ∀ Q : PanelHingeFramework k α β, Q.graph = G.rigidContract H r →
      Q.IsGeneralPosition →
      Q.toBodyHinge.IsInfinitesimallyRigidOn V(G.rigidContract H r) →
      ∃ q_c : α × Fin (k + 2) → ℝ,
        (PanelHingeFramework.ofNormals (G.deleteEdges E(H)) ends q_c).toBodyHinge
          |>.IsInfinitesimallyRigidOn ((V(G) \ V(H)) ∪ {r})) :
    ∃ q_c : α × Fin (k + 2) → ℝ,
      (PanelHingeFramework.ofNormals (G.deleteEdges E(H)) ends q_c).toBodyHinge
        |>.IsInfinitesimallyRigidOn ((V(G) \ V(H)) ∪ {r}) := by
  obtain ⟨Q, hQg, hQgp, hQrank, _⟩ := hQ
  have hne' : Q.toBodyHinge.graph.vertexSet.Nonempty := by
    rw [PanelHingeFramework.toBodyHinge_graph, hQg]; exact hne
  rw [hdef, sub_zero] at hQrank
  have hVeq : V(G.rigidContract H r) = Q.toBodyHinge.graph.vertexSet := by
    rw [PanelHingeFramework.toBodyHinge_graph, hQg]
  have h1 : 1 ≤ V(G.rigidContract H r).ncard := (Set.ncard_pos (Set.toFinite _)).2 hne
  have hQrig : Q.toBodyHinge.IsInfinitesimallyRigidOn V(G.rigidContract H r) := by
    rw [hVeq, BodyHingeFramework.isInfinitesimallyRigidOn_vertexSet_iff_finrank_span_rigidityRows
        Q.toBodyHinge hne', ← hVeq]
    zify [h1] at hQrank ⊢; exact_mod_cast hQrank
  exact htransport Q hQg hQgp hQrig

/-- **The Case-I splice legs `H` and `G ＼ E(H)` cover `G` and share the body `r`** (N6-G3-G3b,
the cover/shared-body/selector geometry of `lem:case-I-realization`; Katoh–Tanigawa 2011 §6.2,
Phase 22a). The graph-combinatorics adapter that discharges the *geometric* inputs of the Case-I
shared-seed coupling (`hasGenericFullRankRealization_of_couple_ofNormals` /
`hasFullRankRealization_of_couple_ofNormals`) from the proper-rigid-subgraph data.

The two splice legs are the rigid block `H` and the surviving-edge subgraph `G ＼ E(H)` (KT's
`R(G,p; E∖E′, V∖V′)`, the contraction leg of the §1.7 recon; *not* the relabelled
`G.rigidContract H r`, which is not `≤ G`). With a chosen representative body `r ∈ V(H)` they meet
the coupling's combinatorial requirements:

* both are subgraphs of `G` (`H ≤ G` from the rigid-subgraph hypothesis; `G ＼ E(H) ≤ G` always);
* `r` is a shared body (`r ∈ V(H)` by choice; `r ∈ V(G ＼ E(H))` since `V(G ＼ E(H)) = V(G)` and
  `r ∈ V(G)` because `V(H) ⊆ V(G)`);
* the legs cover `G` (trivially — `V(G ＼ E(H)) = V(G)`, so the second leg alone covers);
* both legs are nonempty (`V(H)` from the `2 ≤ |V(H)|` conjunct of the proper-rigid
  predicate; `V(G ＼ E(H)) = V(G) ∋ r`).

This is the §1.7 G3b brick: with the `Gc ≤ G` mismatch dissolved at the graph level (the splice's
contraction leg is the literal subgraph `G ＼ E(H)`), the coupling's geometry inputs are pure
graph combinatorics read off `IsProperRigidSubgraph`. The composer (G3c) feeds these facts, the
per-leg rigidities (the `H`-leg IH and the G3a-transported `G ＼ E(H)` leg), and the parent endpoint
selector into the coupling. -/
theorem PanelHingeFramework.couple_geometry_of_isProperRigidSubgraph
    {G H : Graph α β} {r : α} {n : ℕ}
    (hH : H.IsProperRigidSubgraph G n) (hr : r ∈ V(H)) :
    H ≤ G ∧ G.deleteEdges E(H) ≤ G ∧ r ∈ V(H) ∧ r ∈ V(G.deleteEdges E(H)) ∧
      V(G) ⊆ V(H) ∪ V(G.deleteEdges E(H)) ∧ V(H).Nonempty ∧
      V(G.deleteEdges E(H)).Nonempty := by
  have hVHne : V(H).Nonempty := hH.vertexSet_nonempty
  obtain ⟨⟨hle, _⟩, -, hVHss⟩ := hH
  have hrG : r ∈ V(G) := hVHss.subset hr
  have hVc : V(G.deleteEdges E(H)) = V(G) := Graph.vertexSet_deleteEdges G E(H)
  refine ⟨hle, Graph.deleteEdges_le, hr, by rw [hVc]; exact hrG, ?_, hVHne, ?_⟩
  · rw [hVc]; exact fun x hx => Or.inr hx
  · rw [hVc]; exact ⟨r, hrG⟩

/-- **Case I splice producer, *generic* body-set form: legs rigid on per-leg body sets `sH`/`sc`
at a GP seed give a *general-position* full-rank realization** (`lem:case-I-realization`,
the body-set generic splice N6-G3-G3c-iii; Katoh–Tanigawa 2011 §6.2, eqs. (6.3), (6.6), the
"nonparallel, if `G` is simple" strengthening; Phase 22a). The common generalization of the two
N6-G1 / G3c-ii halves: the *generic* motive of `hasGenericFullRankRealization_of_splice_ofNormals`
(N6-G1) combined with the *per-leg body set* `sH`/`sc` of
`hasFullRankRealization_of_splice_set_of_supportExtensor` (G3c-ii).

It is the producer the composer's *simple* Case-I branch needs: KT eq. (6.3)'s contraction block is
rigid only on the surviving bodies `sc = (V(G)∖V(H)) ∪ {r}` (not all of `V(Gc) = V(G)`), so the
all-of-`V(·)` generic splice N6-G1 does not fit; and the bare body-set splice G3c-ii loses general
position through the genericity device (it concludes only the bare motive). This brick keeps both:
the block-triangular splice glue `isInfinitesimallyRigidOn_of_splice` is genericity-free and (at
`t := V(G)`, the cover) makes `ofNormals G ends q₀` rigid on the *parent's* full `V(G)` from the two
body-set-rigid legs, so realizing at the GP seed `q₀` itself keeps the rigidity (from the glue) and
the general position (`hgp`, by hypothesis). No device round-trip. -/
theorem PanelHingeFramework.hasGenericFullRankRealization_of_splice_set_ofNormals
    [Finite α] [Finite β] (G : Graph α β) (ends : β → α × α)
    (hends : ∀ e u v, G.IsLink e u v → G.IsLink e (ends e).1 (ends e).2)
    {q₀ : α × Fin (k + 2) → ℝ}
    (hgp : (PanelHingeFramework.ofNormals G ends q₀).IsGeneralPosition)
    (halg : AlgebraicIndependent ℚ q₀)
    {GH Gc : Graph α β} (hGH : GH ≤ G) (hGc : Gc ≤ G)
    {sH sc : Set α} {c : α} (hcH : c ∈ sH) (hcc : c ∈ sc) (hcover : V(G) ⊆ sH ∪ sc)
    (hblock : (PanelHingeFramework.ofNormals GH ends q₀).toBodyHinge.IsInfinitesimallyRigidOn sH)
    (hcontract :
      (PanelHingeFramework.ofNormals Gc ends q₀).toBodyHinge.IsInfinitesimallyRigidOn sc)
    (n : ℕ) (hne : V(G).Nonempty) (hdef : G.deficiency n = 0) :
    PanelHingeFramework.HasGenericFullRankRealization k n G := by
  set F := (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge with hF
  -- Derive rigidity from the body-set splice glue.
  have hrig : F.IsInfinitesimallyRigidOn V(G) :=
    F.isInfinitesimallyRigidOn_of_splice (GH := GH) (Gc := Gc) (sH := sH) (sc := sc)
      (by rw [hF]; exact hGH) (by rw [hF]; exact hGc) hcH hcc hcover hblock hcontract
  -- Convert rigidity to rank via W2 + hdef.
  have hFG : F.graph.vertexSet = V(G) := by
    rw [hF, PanelHingeFramework.toBodyHinge_graph, PanelHingeFramework.ofNormals_graph]
  have hne' : F.graph.vertexSet.Nonempty := by rw [hFG]; exact hne
  have h1 : 1 ≤ V(G).ncard := (Set.ncard_pos (Set.toFinite _)).2 hne
  have hW2 := F.finrank_span_rigidityRows_of_rigidOn hne' (hFG ▸ hrig)
  have hrank : (Module.finrank ℝ (Submodule.span ℝ F.rigidityRows) : ℤ)
      = screwDim k * ((V(G).ncard : ℤ) - 1) - G.deficiency n := by
    rw [hFG] at hW2; rw [hdef, sub_zero]; zify [h1] at hW2 ⊢; exact_mod_cast hW2
  exact ⟨PanelHingeFramework.ofNormals G ends q₀,
    PanelHingeFramework.ofNormals_graph G ends q₀, hgp, hrank,
    PanelHingeFramework.ofNormals_recordsLinks_of_hends G ends q₀ hends, halg⟩

/-- **Case I shared-seed coupling, *generic* body-set form** (`lem:case-I-realization`, the body-set
generic coupling N6-G3-G3c-iii; Katoh–Tanigawa 2011 §6.2, eqs. (6.3), (6.6), Phase 22a). The
common generalization of the *generic* coupling G2c
(`hasGenericFullRankRealization_of_couple_ofNormals`, all-of-`V(·)` legs) and the *bare* body-set
coupling G3c-ii (`hasFullRankRealization_of_couple_ofNormals_set`): it threads per-leg body sets
`sH`/`sc` through the same five-step witness-transfer as the bare body-set coupling but finishes on
the *generic* body-set splice `hasGenericFullRankRealization_of_splice_set_ofNormals` (realizing at
the shared GP seed `q₀` directly, keeping general position) instead of the device-routing bare
body-set splice. This is the producer the simple Case-I composer feeds to discharge
`theorem_55_generic`'s `hcontractGP` GP conjunct, with the contraction leg rigid only on the
surviving bodies `sc = (V(G)∖V(H)) ∪ {r}`. The complement-isolation equalities `hpinH`/`hpinc` are
discharged per-leg at the composer call site (see `couple_ofNormals_set`).

The parent selector `hends` is taken in the **edge-restricted** form `∀ e u v, G.IsLink e u v →
G.IsLink e (ends e).1 (ends e).2` (N6-G3-G3c-iii-a, design doc §1.11), not the all-`β`
`∀ e, G.IsLink e (ends e).1 (ends e).2`: an all-`β` selector is unsatisfiable for a label type
carrying non-edges, and the body uses `hends` *only* to derive the edge-restricted leg forms
`hendsH`/`hendsc` (everything downstream takes those or the witnessed-index `hsupp`). An
edge-restricted parent selector is constructible from `G` alone (the canonical `Graph.endsOf`, which
links every edge by `isLink_endsOf`), so the composer can supply it. -/
theorem PanelHingeFramework.hasGenericFullRankRealization_of_couple_ofNormals_set
    [Finite α] [Finite β] (G : Graph α β) (ends : β → α × α)
    (hends : ∀ e u v, G.IsLink e u v → G.IsLink e (ends e).1 (ends e).2)
    {GH Gc : Graph α β} (hGH : GH ≤ G) (hGc : Gc ≤ G)
    {sH sc : Set α} {c : α} (hcH : c ∈ sH) (hcc : c ∈ sc) (hcover : V(G) ⊆ sH ∪ sc)
    (hnesH : sH.Nonempty) (hnesc : sc.Nonempty)
    {qH qc : α × Fin (k + 2) → ℝ}
    (hpinH : ∀ q : α × Fin (k + 2) → ℝ, Module.finrank ℝ
      ((PanelHingeFramework.ofNormals GH ends q).toBodyHinge.pinnedMotionsOn sH)
      = screwDim k * sHᶜ.ncard)
    (hpinc : ∀ q : α × Fin (k + 2) → ℝ, Module.finrank ℝ
      ((PanelHingeFramework.ofNormals Gc ends q).toBodyHinge.pinnedMotionsOn sc)
      = screwDim k * scᶜ.ncard)
    (hneH : ∀ e, GH.IsLink e (ends e).1 (ends e).2 →
      (PanelHingeFramework.ofNormals GH ends qH).toBodyHinge.supportExtensor e ≠ 0)
    (hnec : ∀ e, Gc.IsLink e (ends e).1 (ends e).2 →
      (PanelHingeFramework.ofNormals Gc ends qc).toBodyHinge.supportExtensor e ≠ 0)
    (hrigH :
      (PanelHingeFramework.ofNormals GH ends qH).toBodyHinge.IsInfinitesimallyRigidOn sH)
    (hrigc :
      (PanelHingeFramework.ofNormals Gc ends qc).toBodyHinge.IsInfinitesimallyRigidOn sc)
    (n : ℕ) (hne : V(G).Nonempty) (hdef : G.deficiency n = 0) :
    PanelHingeFramework.HasGenericFullRankRealization k n G := by
  classical
  -- The parent's *edge-restricted* `hends` weakens to each leg via `GH ≤ G` / `Gc ≤ G`: a leg-link
  -- is a parent-link, the parent records its endpoints, and `isLink_iff` reads them back as a
  -- leg-link of the same edge (this is the only place the relaxed `hends` is used).
  have hendsH : ∀ e u v, GH.IsLink e u v → GH.IsLink e (ends e).1 (ends e).2 := fun e u v h =>
    (Graph.IsSubgraph.isLink_iff hGH h.edge_mem).mpr
      (hends e u v ((Graph.IsSubgraph.isLink_iff hGH h.edge_mem).mp h))
  have hendsc : ∀ e u v, Gc.IsLink e u v → Gc.IsLink e (ends e).1 (ends e).2 := fun e u v h =>
    (Graph.IsSubgraph.isLink_iff hGc h.edge_mem).mpr
      (hends e u v ((Graph.IsSubgraph.isLink_iff hGc h.edge_mem).mp h))
  -- (i) Each leg's *body-set* leg-restricted rank polynomial at its own seed, with rational
  -- coefficients (`hQHrat`/`hQcrat`).
  obtain ⟨rsH, QH, hsuppH, hcardH, hQ0H, hQHrat, hLIH⟩ :=
    PanelHingeFramework.exists_rankPolynomial_of_rigidOn_linking_set GH ends hendsH hneH hnesH hrigH
  obtain ⟨rsc, Qc, hsuppc, hcardc, hQ0c, hQcrat, hLIc⟩ :=
    PanelHingeFramework.exists_rankPolynomial_of_rigidOn_linking_set Gc ends hendsc hnec hnesc hrigc
  -- (ii) The general-position factor (rational).
  obtain ⟨Qgp, hQgp_ne, hQgprat, hQgp_pos⟩ :=
    exists_generalPosition_polynomial (k := k) G ends
  -- (iii) All three polynomials are rational, so an algebraically-independent-over-`ℚ` seed `q₀` is
  -- a simultaneous non-root, and carries the motive's algebraic-independence conjunct.
  have hQHne : QH ≠ 0 := fun h => hQ0H (by rw [h, map_zero])
  have hQcne : Qc ≠ 0 := fun h => hQ0c (by rw [h, map_zero])
  have hQgpne : Qgp ≠ 0 := by
    obtain ⟨f, hf⟩ := Countable.exists_injective_nat α
    refine fun h => hQgp_ne (fun a => (f a : ℝ)) ?_ (by rw [h, map_zero])
    exact fun a b hab => hf (Nat.cast_injective hab)
  obtain ⟨q₀, _, halg⟩ := exists_injective_algebraicIndependent_real (α × Fin (k + 2))
  have hq₀H : MvPolynomial.eval q₀ QH ≠ 0 :=
    MvPolynomial.eval_ne_zero_of_coeffs_subset_range_of_algebraicIndependent halg hQHrat hQHne
  have hq₀c : MvPolynomial.eval q₀ Qc ≠ 0 :=
    MvPolynomial.eval_ne_zero_of_coeffs_subset_range_of_algebraicIndependent halg hQcrat hQcne
  have hq₀gp : MvPolynomial.eval q₀ Qgp ≠ 0 :=
    MvPolynomial.eval_ne_zero_of_coeffs_subset_range_of_algebraicIndependent halg hQgprat hQgpne
  -- (iv) At `q₀` each leg is rigid *on its body set* (body-set consumer, carrying `hpinH`/`hpinc`),
  -- and the parent normals are general.
  have hrigH₀ :
      (PanelHingeFramework.ofNormals GH ends q₀).toBodyHinge.IsInfinitesimallyRigidOn sH :=
    PanelHingeFramework.isInfinitesimallyRigidOn_ofNormals_of_rankPolynomial_ne_zero_linking_set
      GH ends hnesH (hpinH q₀) hsuppH hcardH hLIH hq₀H
  have hrigc₀ :
      (PanelHingeFramework.ofNormals Gc ends q₀).toBodyHinge.IsInfinitesimallyRigidOn sc :=
    PanelHingeFramework.isInfinitesimallyRigidOn_ofNormals_of_rankPolynomial_ne_zero_linking_set
      Gc ends hnesc (hpinc q₀) hsuppc hcardc hLIc hq₀c
  have hgp : (PanelHingeFramework.ofNormals (k := k) G ends q₀).IsGeneralPosition :=
    hQgp_pos q₀ hq₀gp
  -- (v) The *generic* body-set splice: realize at the alg-indep GP seed `q₀` itself (bypassing the
  -- device), so general position survives and the conclusion is the strengthened generic motive.
  exact PanelHingeFramework.hasGenericFullRankRealization_of_splice_set_ofNormals G ends hends hgp
    halg hGH hGc hcH hcc hcover hrigH₀ hrigc₀ n hne hdef

/-- **Case I shared-seed coupling, *asymmetric* body-set form** (`lem:case-I-realization`, the
asymmetric coupling N6-G3-G3c-iii-b; Katoh–Tanigawa 2011 §6.2, eqs. (6.3), (6.6), (6.9), Phase 22a).
The fix for the two-leg coupling KT Case I actually needs (design doc §1.12). The *symmetric*
`hasGenericFullRankRealization_of_couple_ofNormals_set` runs **both** legs through the body-set
rank-polynomial round-trip, and the body-set consumer it calls
(`isInfinitesimallyRigidOn_ofNormals_of_rankPolynomial_ne_zero_linking_set`) needs each leg's
complement-isolation equality `hpin : finrank (pinnedMotionsOn s) = D·|sᶜ|`. For the **rigid block**
leg `GH` rigid on its *full* vertex set `sH = V(GH)` that equality is the green
`finrank_pinnedMotionsOn_vertexSet`; but for the **contraction** leg `Gc = G ＼ E(H)` rigid only on
the surviving bodies `sc = (V(G)∖V(H))∪{r}` ⊊ `V(Gc) = V(G)`, the equality is **false** — the
interior bodies `V(H)∖{r}` are *not* isolated in `G ＼ E(H)` (surviving boundary edges
`δ_G(V(H))` constrain them; the project's `finrank_pinnedMotionsOn_le` proves only the *upper*
bound). So the symmetric coupling forces a false hypothesis on the contraction leg.

This asymmetric coupling matches KT eq. (6.6), which constructs **one** placement for all of `G`
(it does *not* intersect two Zariski-open rigid loci): the `H`-leg's generic placement determines
the shared seed, and the contraction leg's rigidity is read off *at that one seed* by Claim 6.4
(eq. (6.9)). So the `H`-leg keeps the green round-trip — its rank polynomial `Q_H`
(`exists_rankPolynomial_of_rigidOn_linking_set`) × the general-position factor `Q_gp`
(`exists_generalPosition_polynomial`) produces the shared general-position non-root `q₀` — and the
contraction leg's rigidity at `q₀` on `sc` is supplied **directly** by the Claim-6.4 hypothesis
`hrigcGP`, *not* re-derived through the body-set N3 consumer. `hrigcGP` is quantified over all
general-position seeds (matching KT eq. (6.9)'s "the rank is attained at generic placements"),
decoupling the contraction obligation from the `H`-leg's internal seed search. The contraction leg
therefore carries **no `hpinc`**, **no body-set rank polynomial**, and **no own-seed rigidity** —
only the genuine Claim-6.4 content. Both `q₀`-rigid legs feed the generic body-set splice
`hasGenericFullRankRealization_of_splice_set_ofNormals` directly.

The parent selector `hends` is the edge-restricted form (N6-G3-G3c-iii-a, design doc §1.11), as in
the symmetric coupling. -/
theorem PanelHingeFramework.hasGenericFullRankRealization_of_couple_asymm_ofNormals_set
    [Finite α] [Finite β] (G : Graph α β) (ends : β → α × α)
    (hends : ∀ e u v, G.IsLink e u v → G.IsLink e (ends e).1 (ends e).2)
    {GH Gc : Graph α β} (hGH : GH ≤ G) (hGc : Gc ≤ G)
    {sH sc : Set α} {c : α} (hcH : c ∈ sH) (hcc : c ∈ sc) (hcover : V(G) ⊆ sH ∪ sc)
    (hnesH : sH.Nonempty)
    {qH : α × Fin (k + 2) → ℝ}
    (hpinH : ∀ q : α × Fin (k + 2) → ℝ, Module.finrank ℝ
      ((PanelHingeFramework.ofNormals GH ends q).toBodyHinge.pinnedMotionsOn sH)
      = screwDim k * sHᶜ.ncard)
    (hneH : ∀ e, GH.IsLink e (ends e).1 (ends e).2 →
      (PanelHingeFramework.ofNormals GH ends qH).toBodyHinge.supportExtensor e ≠ 0)
    (hrigH :
      (PanelHingeFramework.ofNormals GH ends qH).toBodyHinge.IsInfinitesimallyRigidOn sH)
    -- The contraction leg's rigidity on `sc`, supplied **directly** at every general-position seed
    -- (KT eq. (6.9) / Claim 6.4 — the rank is attained at generic placements). No body-set N3, no
    -- `hpinc`, no rank-polynomial round-trip for this leg.
    (hrigcGP : ∀ q : α × Fin (k + 2) → ℝ,
      (PanelHingeFramework.ofNormals (k := k) G ends q).IsGeneralPosition →
      (PanelHingeFramework.ofNormals Gc ends q).toBodyHinge.IsInfinitesimallyRigidOn sc)
    (n : ℕ) (hne : V(G).Nonempty) (hdef : G.deficiency n = 0) :
    PanelHingeFramework.HasGenericFullRankRealization k n G := by
  classical
  -- The parent's edge-restricted `hends` weakens to the `H`-leg via `GH ≤ G` (the only leg that
  -- runs the rank-polynomial round-trip; the contraction leg is fed `hrigcGP` directly).
  have hendsH : ∀ e u v, GH.IsLink e u v → GH.IsLink e (ends e).1 (ends e).2 := fun e u v h =>
    (Graph.IsSubgraph.isLink_iff hGH h.edge_mem).mpr
      (hends e u v ((Graph.IsSubgraph.isLink_iff hGH h.edge_mem).mp h))
  -- (i) The `H`-leg's body-set leg-restricted rank polynomial at its own seed (rational).
  obtain ⟨rsH, QH, hsuppH, hcardH, hQ0H, hQHrat, hLIH⟩ :=
    PanelHingeFramework.exists_rankPolynomial_of_rigidOn_linking_set GH ends hendsH hneH hnesH hrigH
  -- (ii) The general-position factor (rational).
  obtain ⟨Qgp, hQgp_ne, hQgprat, hQgp_pos⟩ :=
    exists_generalPosition_polynomial (k := k) G ends
  -- (iii) Both `Q_H` and `Q_gp` are rational, so an algebraically-independent-over-`ℚ` seed `q₀` is
  -- a simultaneous non-root, and carries the motive's algebraic-independence conjunct.
  have hQHne : QH ≠ 0 := fun h => hQ0H (by rw [h, map_zero])
  have hQgpne : Qgp ≠ 0 := by
    obtain ⟨f, hf⟩ := Countable.exists_injective_nat α
    refine fun h => hQgp_ne (fun a => (f a : ℝ)) ?_ (by rw [h, map_zero])
    exact fun a b hab => hf (Nat.cast_injective hab)
  obtain ⟨q₀, _, halg⟩ := exists_injective_algebraicIndependent_real (α × Fin (k + 2))
  have hq₀H : MvPolynomial.eval q₀ QH ≠ 0 :=
    MvPolynomial.eval_ne_zero_of_coeffs_subset_range_of_algebraicIndependent halg hQHrat hQHne
  have hq₀gp : MvPolynomial.eval q₀ Qgp ≠ 0 :=
    MvPolynomial.eval_ne_zero_of_coeffs_subset_range_of_algebraicIndependent halg hQgprat hQgpne
  -- (iv) The parent normals are general at `q₀`.
  have hgp : (PanelHingeFramework.ofNormals (k := k) G ends q₀).IsGeneralPosition :=
    hQgp_pos q₀ hq₀gp
  -- The `H`-leg is rigid on `sH` at `q₀` (body-set consumer, with the honest `hpinH`).
  have hrigH₀ :
      (PanelHingeFramework.ofNormals GH ends q₀).toBodyHinge.IsInfinitesimallyRigidOn sH :=
    PanelHingeFramework.isInfinitesimallyRigidOn_ofNormals_of_rankPolynomial_ne_zero_linking_set
      GH ends hnesH (hpinH q₀) hsuppH hcardH hLIH hq₀H
  -- The contraction leg is rigid on `sc` at `q₀` **directly** from `hrigcGP` (KT Claim 6.4); the
  -- general-position non-root `q₀` is exactly the generic seed `hrigcGP` quantifies over.
  have hrigc₀ :
      (PanelHingeFramework.ofNormals Gc ends q₀).toBodyHinge.IsInfinitesimallyRigidOn sc :=
    hrigcGP q₀ hgp
  -- (v) The generic body-set splice: realize at the alg-indep GP seed `q₀` itself.
  exact PanelHingeFramework.hasGenericFullRankRealization_of_splice_set_ofNormals G ends hends hgp
    halg hGH hGc hcH hcc hcover hrigH₀ hrigc₀ n hne hdef

/-- **The exterior-column projection** (`lem:case-I-realization` Piece B infra, the block-triangular
core; Katoh–Tanigawa 2011 §6.2, eq. (6.3), Phase 22a). The linear map on screw assignments that
**zeroes out the bodies of `t`** (the rigid block `V(H)`) and keeps the rest: `extProj t S a = 0`
for `a ∈ t`, `= S a` otherwise. Its dual map (precomposition) `(extProj t).dualMap` projects a
rigidity-row functional onto its dependence on the **exterior columns** `α ∖ t`.

This is the column-side of KT eq. (6.3)'s block-triangular split: a rigidity row carried by an
edge of the rigid block `H` (both endpoints in `V(H) = t`) reads only the `t`-columns, so it
**vanishes** under `extProj t` (`hingeRow_comp_extProj_eq_zero`); a surviving edge's row generally
does not. Projecting onto the exterior columns therefore separates the `H`-block rows (which land in
the kernel) from the surviving-edge rows, exactly the top-right `0` of KT's block-triangular matrix.
The Case-II/III analogue is the *pin-a-body* column split `linearIndependent_sum_pinned_block`
(N7b-3); here the "pinned" columns are the whole rigid block `V(H)` rather than a single body. -/
noncomputable def extProj (t : Set α) :
    (α → ScrewSpace k) →ₗ[ℝ] (α → ScrewSpace k) := by
  classical
  exact LinearMap.pi fun a =>
    if a ∈ t then (0 : (α → ScrewSpace k) →ₗ[ℝ] ScrewSpace k) else LinearMap.proj a

theorem extProj_apply_mem {t : Set α} {a : α} (ha : a ∈ t) (S : α → ScrewSpace k) :
    extProj t S a = 0 := by
  classical
  rw [extProj, LinearMap.pi_apply, if_pos ha, LinearMap.zero_apply]

theorem extProj_apply_not_mem {t : Set α} {a : α} (ha : a ∉ t) (S : α → ScrewSpace k) :
    extProj t S a = S a := by
  classical
  rw [extProj, LinearMap.pi_apply, if_neg ha, LinearMap.proj_apply]

/-- **The exterior-column projection is invariant under the collapse relabel**
(`lem:claim-6-4`, the U2 collapse-relabel reconciliation core; Katoh–Tanigawa 2011 §6.2, eq. (6.7),
Phase 22b). For the collapse map `f = collapseTo r t` with the representative `r ∈ t`, the projected
assignment reads the *same* value at a body `a` and at its collapsed image `f a`:
`extProj t S (collapseTo r t a) = extProj t S a`. The two cases reconcile because the projection
kills exactly the collapsed bodies: if `a ∈ t` then `f a = r ∈ t`, and both sides are `0`
(`extProj_apply_mem`); if `a ∉ t` then `f a = a` and both sides are `S a`. This columnwise
invariance is precisely what lets the exterior projection *reconcile* the collapse relabel of KT
eq. (6.7) — the uncollapsed hinge row `hingeRow u v r` and the collapsed `hingeRow (f u) (f v) r`
agree after `(extProj t).dualMap`, even though their endpoints differ on the interior block `t`. -/
theorem extProj_apply_collapseTo {t : Set α} {r : α} (hr : r ∈ t) (S : α → ScrewSpace k) (a : α) :
    extProj t S (Graph.collapseTo r t a) = extProj t S a := by
  classical
  unfold Graph.collapseTo
  split_ifs with ha
  · rw [extProj_apply_mem hr, extProj_apply_mem ha]
  · rfl

/-- **A rigid-block row vanishes under the exterior-column projection** (`lem:case-I-realization`
Piece B fact 2, the row-side of KT eq. (6.3)'s top-right `0`; Phase 22a). If both endpoints `u, v`
of a hinge lie in the rigid block `t = V(H)`, the row functional `hingeRow u v r` precomposed with
the exterior-column projection `extProj t` is the zero functional: `extProj t S` reads `0` at both
`u ∈ t` and `v ∈ t`, so `hingeRow u v r (extProj t S) = r (0 − 0) = 0`. Hence
`(extProj t).dualMap (hingeRow u v r) = 0`, i.e. every `H`-block rigidity row lies in
`ker (extProj t).dualMap`. -/
theorem hingeRow_comp_extProj_eq_zero {t : Set α} {u v : α} (hu : u ∈ t) (hv : v ∈ t)
    (r : Module.Dual ℝ (ScrewSpace k)) :
    (BodyHingeFramework.hingeRow (k := k) (α := α) u v r).comp (extProj t) = 0 := by
  ext S
  rw [LinearMap.comp_apply, LinearMap.zero_apply, BodyHingeFramework.hingeRow_apply,
    extProj_apply_mem hu, extProj_apply_mem hv, sub_zero, map_zero]

/-- **The exterior-column projection reconciles the collapse relabel of a hinge row**
(`lem:claim-6-4`, the U2 collapse-relabel projected-row reproduction; Katoh–Tanigawa 2011 §6.2,
eqs. (6.7)/(6.9), Phase 22b — the one research-shaped Case-I brick). This is the column-side of KT's
algebraic-independence Claim 6.4: an *uncollapsed* hinge row `hingeRow u v ρ` (the surviving edge's
row at its original endpoints) and its *collapsed* relabel `hingeRow (f u) (f v) ρ` (the same row
after the rigid block `t = V(H)` is identified to the representative `r`) become the **same**
functional once projected onto the exterior columns by `(extProj t).dualMap`, provided `r ∈ t`.

The relabel is genuine — a surviving edge `e = uv` with `u ∈ t` reads `S u − S v` uncollapsed but
`S r − S (f v)` collapsed — yet the exterior projection zeroes column `u ∈ t` *and* column
`f u = r ∈ t` (`extProj_apply_collapseTo`), so the two rows read identically on the surviving
columns. This is exactly the reconciliation §1.7's collapse-normal mismatch identified as the
irreducible content of Claim 6.4, now isolated to a row equality across the relabel: it is what
carries the contraction's rigid-row independence (read off `Qcf` over `Gc.map f`) back to the
exterior-projected uncollapsed rows at the degenerate witness placement. -/
theorem hingeRow_collapseTo_comp_extProj_eq {t : Set α} {r : α} (hr : r ∈ t) (u v : α)
    (ρ : Module.Dual ℝ (ScrewSpace k)) :
    (BodyHingeFramework.hingeRow (k := k) (α := α) (Graph.collapseTo r t u)
        (Graph.collapseTo r t v) ρ).comp (extProj t)
      = (BodyHingeFramework.hingeRow (k := k) (α := α) u v ρ).comp (extProj t) := by
  ext S
  rw [LinearMap.comp_apply, LinearMap.comp_apply, BodyHingeFramework.hingeRow_apply,
    BodyHingeFramework.hingeRow_apply, extProj_apply_collapseTo hr, extProj_apply_collapseTo hr]

/-- **The degenerate collapsed placement `q₀^deg`** (`lem:claim-6-4`, the U1 degenerate witness
bridge; Katoh–Tanigawa 2011 §6.2, eq. (6.7)'s `p2`, Phase 22b). The placement on the *original*
body type `α` that pulls a contraction realization's normals back through the collapse map
`f = collapseTo r V(H)`: it assigns each parent body `a` the panel normal `nrm (f a)` of its
collapsed image — so bodies of the rigid block `V(H)` all share the single representative normal
`nrm r` (KT's `p2`: all H-side panels forced equal to the `v∗` panel), and a surviving body
`a ∈ V(G)∖V(H)` keeps its own `nrm a`. This is the *degenerate member* of KT's family embedding
(6.7): not globally general position (the `V(H)` normals coincide), but a valid single witness for
the existential `htransport` — no generic placement needed (design doc §1.19, Finding 2). Built as
a plain pullback `(a, i) ↦ nrm (f a) i`; the reproduction `degeneratePlacement_ofNormals_normal`
records that `ofNormals` at this placement has normal `nrm ∘ f`. (Not a `@[simp]` lemma: its
left-hand side `(ofNormals … (degeneratePlacement …)).normal a` is already reducible by the existing
`ofNormals_normal` simp lemma — `@[simp]` here is redundant and not in simp-normal form — so it is
called by name from the row reproduction below.) -/
noncomputable def degeneratePlacement (r : α) (t : Set α) (nrm : α → Fin (k + 2) → ℝ) :
    α × Fin (k + 2) → ℝ :=
  fun p => nrm (Graph.collapseTo r t p.1) p.2

theorem degeneratePlacement_ofNormals_normal (G : Graph α β) (ends : β → α × α) (r : α) (t : Set α)
    (nrm : α → Fin (k + 2) → ℝ) (a : α) :
    (PanelHingeFramework.ofNormals (k := k) G ends
        (degeneratePlacement r t nrm)).normal a = nrm (Graph.collapseTo r t a) := by
  rw [PanelHingeFramework.ofNormals_normal]
  rfl

/-- **The exterior-projected uncollapsed row reproduces the projected collapsed row at `q₀^deg`**
(`lem:claim-6-4`, the U2 collapse-relabel projected-row reproduction; Katoh–Tanigawa 2011 §6.2,
eqs. (6.7)/(6.9), Phase 22b — the research-shaped Case-I row brick, lifted from the U2 column core
`hingeRow_collapseTo_comp_extProj_eq` to a full per-edge `panelRow` equality). For the degenerate
placement `q₀^deg = degeneratePlacement r V(H) nrm` and any index `i = (e, t₁, t₂)`, the
exterior-column projection of the *uncollapsed* surviving-edge panel row of
`ofNormals Gc ends q₀^deg` (endpoints `(ends e).1, (ends e).2` over the original bodies) **equals**
the exterior-column projection of the *collapsed* panel row of `ofNormals (Gc.map f) endsᶠ q₀^deg'`
over the contracted graph — the row at the relabelled endpoints `(f (ends e).1, f (ends e).2)`
carried by the *same* normals `nrm` and selector `endsᶠ e = (f (ends e).1, f (ends e).2)`.

This is the column-side of KT eq. (6.7)/(6.9) lifted across the support-extensor / selector
framings. The two `panelRow`s differ only in their `hingeRow` endpoints — the uncollapsed `(ends e)`
vs. the relabelled `(f (ends e))` — *and* in nothing else: both read the *same* panel support
extensor `panelSupportExtensor (nrm (f (ends e).1)) (nrm (f (ends e).2))` (the degenerate
placement's normal is `nrm ∘ f` in both framings, so the support extensor at `e` is the collapsed
one on both sides), hence the *same* annihilator functional `ρ = annihRow … i.2.1 i.2.2`. The column
core `hingeRow_collapseTo_comp_extProj_eq` then reconciles the differing endpoints under
`(extProj V(H)).dualMap`, since the projection reads the same value at a body and its collapsed
image (`extProj_apply_collapseTo`). This is §1.7's irreducible collapse-normal mismatch isolated to
a single row equality across the relabel — the step that, fed an independent surviving subfamily of
the contraction (U3), carries that independence back to the exterior-projected uncollapsed rows. -/
theorem panelRow_collapseTo_comp_extProj_dualMap (Gc H : Graph α β) {r : α} (hr : r ∈ V(H))
    (nrm : α → Fin (k + 2) → ℝ) (ends : β → α × α)
    (i : β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k) :
    (extProj (k := k) V(H)).dualMap
        ((PanelHingeFramework.ofNormals Gc ends
          (degeneratePlacement r V(H) nrm)).toBodyHinge.panelRow ends i)
      = (extProj (k := k) V(H)).dualMap
        ((PanelHingeFramework.ofNormals (Gc.map (Graph.collapseTo r V(H)))
            (fun e => (Graph.collapseTo r V(H) (ends e).1, Graph.collapseTo r V(H) (ends e).2))
            (fun p => nrm p.1 p.2)).toBodyHinge.panelRow
          (fun e =>
            (Graph.collapseTo r V(H) (ends e).1, Graph.collapseTo r V(H) (ends e).2)) i) := by
  rw [BodyHingeFramework.panelRow, BodyHingeFramework.panelRow,
    PanelHingeFramework.toBodyHinge_supportExtensor,
    PanelHingeFramework.toBodyHinge_supportExtensor,
    PanelHingeFramework.ofNormals_ends, PanelHingeFramework.ofNormals_ends,
    PanelHingeFramework.ofNormals_normal, PanelHingeFramework.ofNormals_normal,
    PanelHingeFramework.ofNormals_normal, PanelHingeFramework.ofNormals_normal,
    LinearMap.dualMap_apply', LinearMap.dualMap_apply']
  dsimp only [degeneratePlacement]
  exact (hingeRow_collapseTo_comp_extProj_eq (k := k) (α := α) hr (ends i.1).1 (ends i.1).2 _).symm

/-- **The range of the exterior-column projection is the kernel of the `proj`-projections**
(`lem:claim-6-4`, the U3b dual-annihilator assembly infra; Katoh–Tanigawa 2011 §6.2, Phase 22b).
The exterior-column projection `extProj proj` zeroes the `proj` columns and keeps the rest, so its
range is exactly the screw assignments **vanishing on `proj`**: `range (extProj proj) =
⨅ i ∈ proj, ker (proj i)`. `extProj proj` is idempotent (it is a coordinate projection), so an
assignment `T` lies in the range iff `extProj proj T = T`, i.e.\ iff `T a = 0` for every `a ∈ proj`
(`extProj_apply_mem`/`extProj_apply_not_mem`). This identifies the range as the `iInf`-of-kernels
whose dimension is the free-isolated count `D·|projᶜ|` (`finrank_iInf_ker_proj_eq`), the `W`-term of
the §1.22 `Z ⊔ W = ⊤` count. -/
theorem extProj_range_eq_iInf_ker_proj (proj : Set α) :
    LinearMap.range (extProj (k := k) proj) =
      ⨅ i ∈ proj, LinearMap.ker (LinearMap.proj i : (α → ScrewSpace k) →ₗ[ℝ] ScrewSpace k) := by
  classical
  ext T
  simp only [LinearMap.mem_range, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.proj_apply]
  constructor
  · rintro ⟨S, rfl⟩ i hi
    exact extProj_apply_mem hi S
  · intro hT
    refine ⟨T, ?_⟩
    funext a
    by_cases ha : a ∈ proj
    · rw [extProj_apply_mem ha, (hT a ha).symm]
    · rw [extProj_apply_not_mem ha]

/-- **The trivial-and-pinned intersection is the block pin** (`lem:claim-6-4`, the U3b
dual-annihilator assembly infra; Katoh–Tanigawa 2011 §6.2, Phase 22b). The intersection of the
infinitesimal motions `Z = infinitesimalMotions` with the exterior-projection range
`W = range (extProj proj)` is exactly the block pin `pinnedMotionsOn proj`: a member of `Z` is an
infinitesimal motion, a member of `W` vanishes on `proj` (`extProj_range_eq_iInf_ker_proj`), and an
assignment is both iff it is a motion vanishing on `proj` — the defining conjunction of
`pinnedMotionsOn proj`. This is the `Z ⊓ W` term of the §1.22 inclusion–exclusion. -/
theorem infinitesimalMotions_inf_range_extProj_eq_pinnedMotionsOn
    (F : BodyHingeFramework k α β) (proj : Set α) :
    F.infinitesimalMotions ⊓ LinearMap.range (extProj (k := k) proj) = F.pinnedMotionsOn proj := by
  classical
  ext S
  rw [Submodule.mem_inf, extProj_range_eq_iInf_ker_proj]
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.proj_apply, F.mem_pinnedMotionsOn,
    F.mem_infinitesimalMotions S]

/-- **A framework rigid on its full vertex set, pinned at a block meeting `V(G)` in one body, spans
together with the exterior-projection range** (`lem:claim-6-4`, the U3b `Z ⊔ W = ⊤` dual-annihilator
assembly — the closing finrank count of the exterior-rank discharge; Katoh–Tanigawa 2011 §6.2
eqs.\ (6.5)/(6.9), §5.1, Phase 22b). For `F` infinitesimally rigid on its whole vertex set `V(G)`
and a block `proj` meeting `V(G)` in exactly the representative body `r` (`V(G) ∩ proj = {r}`), the
infinitesimal motions `Z = infinitesimalMotions` and the exterior-projection range
`W = range (extProj proj)` **jointly span everything**: `Z ⊔ W = ⊤`.

This is the §1.22 closing fact: `Z ⊔ W = ⊤` is what makes the exterior-column projection
`(extProj proj).dualMap` injective on the rigidity-row span `Φ`
(`Φ ⊓ ker D = (Z ⊔ W).dualAnnihilator = ⊥`), so the projection loses *zero* rank and the surviving
block keeps its independent rank `D(|sc|−1)` (KT Claim 6.4 proper). It is proved by the finrank
count `finrank(Z ⊔ W) + finrank(Z ⊓ W) = finrank Z + finrank W`
(`Submodule.finrank_sup_add_finrank_inf_eq`) using the three confirmed dimensions:
`finrank Z = D(|V(G)ᶜ| + 1)` (rigid-on-vertexSet,
`finrank_infinitesimalMotions_of_isInfinitesimallyRigidOn_vertexSet`),
`finrank W = D·|projᶜ|` (`extProj_range_eq_iInf_ker_proj` + `finrank_iInf_ker_proj_eq`), and the
rigid-block pin-count `finrank(Z ⊓ W) = finrank(pinnedMotionsOn proj) = D(|V(G)ᶜ| + 1 − |proj|)`
(`infinitesimalMotions_inf_range_extProj_eq_pinnedMotionsOn` + the §1.22 walling node
`finrank_pinnedMotionsOn_of_isInfinitesimallyRigidOn_vertexSet_inter_eq_singleton`). The sum forces
`finrank(Z ⊔ W) = D·|α| = finrank (α → ScrewSpace k)`, whence `Z ⊔ W = ⊤`. -/
theorem infinitesimalMotions_sup_range_extProj_eq_top
    [Finite α] (F : BodyHingeFramework k α β) {proj : Set α} {r : α}
    (hrig : F.IsInfinitesimallyRigidOn F.graph.vertexSet)
    (hr : r ∈ F.graph.vertexSet) (hinter : F.graph.vertexSet ∩ proj = {r}) :
    F.infinitesimalMotions ⊔ LinearMap.range (extProj (k := k) proj) = ⊤ := by
  classical
  haveI : Fintype α := Fintype.ofFinite α
  -- The three confirmed dimensions of the §1.22 inclusion–exclusion.
  have hZ : Module.finrank ℝ F.infinitesimalMotions
      = screwDim k * ((F.graph.vertexSet)ᶜ.ncard + 1) :=
    F.finrank_infinitesimalMotions_of_isInfinitesimallyRigidOn_vertexSet ⟨r, hr⟩ hrig
  have hW : Module.finrank ℝ (LinearMap.range (extProj (k := k) proj))
      = screwDim k * projᶜ.ncard := by
    rw [extProj_range_eq_iInf_ker_proj, BodyHingeFramework.finrank_iInf_ker_proj_eq]
  have hinf : Module.finrank ℝ
      (F.infinitesimalMotions ⊓ LinearMap.range (extProj (k := k) proj) :
        Submodule ℝ (α → ScrewSpace k))
      = screwDim k * ((F.graph.vertexSet)ᶜ.ncard + 1 - proj.ncard) := by
    rw [infinitesimalMotions_inf_range_extProj_eq_pinnedMotionsOn,
      F.finrank_pinnedMotionsOn_of_isInfinitesimallyRigidOn_vertexSet_inter_eq_singleton
        hrig hr hinter]
  -- `finrank (Z ⊔ W) + finrank (Z ⊓ W) = finrank Z + finrank W` (mathlib).
  have hadd := Submodule.finrank_sup_add_finrank_inf_eq F.infinitesimalMotions
    (LinearMap.range (extProj (k := k) proj))
  rw [hZ, hW, hinf] at hadd
  -- `|proj| ≤ |V(G)ᶜ| + 1`: `proj ⊆ {r} ∪ V(G)ᶜ`.
  have hpcard : proj.ncard ≤ (F.graph.vertexSet)ᶜ.ncard + 1 := by
    have hsub : proj ⊆ {r} ∪ (F.graph.vertexSet)ᶜ := by
      intro a ha
      by_cases hav : a ∈ F.graph.vertexSet
      · left; exact (Set.ext_iff.1 hinter a).1 ⟨hav, ha⟩
      · right; exact hav
    calc proj.ncard ≤ ({r} ∪ (F.graph.vertexSet)ᶜ).ncard :=
          Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ ({r} : Set α).ncard + (F.graph.vertexSet)ᶜ.ncard := Set.ncard_union_le _ _
      _ = (F.graph.vertexSet)ᶜ.ncard + 1 := by rw [Set.ncard_singleton]; ring
  -- The complement count `|projᶜ| = |α| − |proj|`, and the `ncard`-level inclusion–exclusion.
  have hcompl : proj.ncard + projᶜ.ncard = Fintype.card α := by
    rw [Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card]
  have hcount : (F.graph.vertexSet)ᶜ.ncard + 1 + projᶜ.ncard
      = Fintype.card α + ((F.graph.vertexSet)ᶜ.ncard + 1 - proj.ncard) := by omega
  -- Distribute `D` over the count identity, then rewrite `hadd` to read off `finrank (Z ⊔ W)`.
  refine Submodule.eq_top_of_finrank_eq ?_
  rw [BodyHingeFramework.finrank_screwAssignment]
  have hdist : screwDim k * ((F.graph.vertexSet)ᶜ.ncard + 1) + screwDim k * projᶜ.ncard
      = screwDim k * Fintype.card α
        + screwDim k * ((F.graph.vertexSet)ᶜ.ncard + 1 - proj.ncard) := by
    rw [← Nat.mul_add, ← Nat.mul_add, hcount]
  omega

/-- **The exterior-column projection is injective on the rigidity-row span of a rigid block**
(`lem:claim-6-4`, the U3b dual-annihilator core — the projection loses zero rank; Katoh–Tanigawa
2011 §6.2 eqs.\ (6.5)/(6.9), Phase 22b). For `F` infinitesimally rigid on its whole vertex set
`V(G)` and a block `proj` meeting `V(G)` in exactly the representative body `r`, the exterior-column
projection's dual map `D = (extProj proj).dualMap` is **injective on the rigidity-row span**
`Φ = span rigidityRows`. This is the §1.22 closing fact in injective form: `Φ ⊓ ker D = ⊥`.

The chain is pure dual API on top of the `Z ⊔ W = ⊤` count
(`infinitesimalMotions_sup_range_extProj_eq_top`, `Z = infinitesimalMotions`,
`W = range (extProj proj)`):
* `ker D = W.dualAnnihilator` (`LinearMap.ker_dualMap_eq_dualAnnihilator_range`);
* `Φ = Z.dualAnnihilator` — `Z = Φ.dualCoannihilator` (`infinitesimalMotions_eq_dualCoannihilator`)
  and the finite-dim double-annihilator `dualCoannihilator_dualAnnihilator_eq`;
* `Φ ⊓ ker D = Z.dualAnnihilator ⊓ W.dualAnnihilator = (Z ⊔ W).dualAnnihilator`
  (`Submodule.dualAnnihilator_sup_eq`) `= ⊤.dualAnnihilator = ⊥` (`dualAnnihilator_top`).
Disjointness from the kernel is exactly injectivity on `Φ`
(`Submodule.disjoint_ker_iff_injOn`). -/
theorem BodyHingeFramework.injOn_extProj_dualMap_rigidityRows
    [Finite α] (F : BodyHingeFramework k α β) {proj : Set α} {r : α}
    (hrig : F.IsInfinitesimallyRigidOn F.graph.vertexSet)
    (hr : r ∈ F.graph.vertexSet) (hinter : F.graph.vertexSet ∩ proj = {r}) :
    Set.InjOn (extProj (k := k) proj).dualMap (Submodule.span ℝ F.rigidityRows) := by
  classical
  haveI : Fintype α := Fintype.ofFinite α
  -- `Φ = Z.dualAnnihilator` (double annihilator) and `ker D = W.dualAnnihilator`, so
  -- `Φ ⊓ ker D = (Z ⊔ W).dualAnnihilator = ⊤.dualAnnihilator = ⊥`.
  have hΦeq : Submodule.span ℝ F.rigidityRows
      = F.infinitesimalMotions.dualAnnihilator := by
    rw [F.infinitesimalMotions_eq_dualCoannihilator,
      Subspace.dualCoannihilator_dualAnnihilator_eq]
  refine LinearMap.injOn_of_disjoint_ker le_rfl ?_
  rw [disjoint_iff, LinearMap.ker_dualMap_eq_dualAnnihilator_range, hΦeq,
    ← Submodule.dualAnnihilator_sup_eq,
    infinitesimalMotions_sup_range_extProj_eq_top F hrig hr hinter,
    Submodule.dualAnnihilator_top]

/-- **The motions and the exterior-projection range jointly span everything — at ANY rank, no
rigidity** (`lem:rigidityRows-splice-rank-add`, the genuinely-new general-rank input of the L5a
splice brick; Katoh–Tanigawa 2011 §6.2, eq. (6.5) / Lemma 5.1, Phase 22i L5a-ii). The
**deficiency-tolerant** sibling of `infinitesimalMotions_sup_range_extProj_eq_top`: for *any*
body-hinge framework `F` and a block `proj` meeting the vertex set in exactly the representative
body `r` (`V(G) ∩ proj = {r}`), the infinitesimal motions `Z = infinitesimalMotions` and the
exterior-projection range `W = range (extProj proj)` **jointly span everything**: `Z ⊔ W = ⊤`.

Unlike the rigid sibling — which routes through the `Z ⊔ W` *finrank count* and needs full
rigidity to pin the residual at `D(|V(G)ᶜ| + 1 − |proj|)` — this proves `Z ⊔ W = ⊤` by an
**explicit decomposition** that needs no rank input at all. For any assignment `S`, set the
"flattened-on-`V(G)`" motion `z a := if a ∈ V(G) then S r else S a`: `z` is an infinitesimal motion
(every constraint has both endpoints in `V(G)`, where `z` is the constant `S r`, so the relative
screw `z u − z v = 0 ∈ span C(p(e))`), and the residual `S − z` vanishes on `proj` (on `r`:
`S r − S r = 0`; on `proj ∖ {r} ⊆ V(G)ᶜ`: `z a = S a`, so `S a − z a = 0`), hence lies in
`W = ⨅ i ∈ proj, ker (proj i)` (`extProj_range_eq_iInf_ker_proj`). This is the algebraic
content KT (6.5) invokes through Lemma 5.1: deleting the single shared body `r`'s columns
(`extProj proj` zeroes exactly column `r` of the contraction's own bodies, since
`V(G) ∩ proj = {r}`) preserves rank because the only `Z`-motion lost to the projection is the
trivial `S r`-shift, recovered by the constant-on-`V(G)` motion `z`. -/
theorem infinitesimalMotions_sup_range_extProj_eq_top_of_inter_eq_singleton
    [Finite α] (F : BodyHingeFramework k α β) {proj : Set α} {r : α}
    (hinter : F.graph.vertexSet ∩ proj = {r}) :
    F.infinitesimalMotions ⊔ LinearMap.range (extProj (k := k) proj) = ⊤ := by
  classical
  rw [eq_top_iff]
  intro S _
  rw [Submodule.mem_sup]
  -- The "flattened-on-`V(G)`" motion: constant `S r` on `V(G)`, equal to `S` off `V(G)`.
  refine ⟨fun a => if a ∈ F.graph.vertexSet then S r else S a, ?_,
    fun a => if a ∈ F.graph.vertexSet then S a - S r else 0, ?_, ?_⟩
  · -- `z` is an infinitesimal motion: every edge's endpoints lie in `V(G)`, where `z = S r`.
    intro e u v he
    rw [BodyHingeFramework.hingeConstraint, if_pos he.left_mem, if_pos he.right_mem, sub_self]
    exact Submodule.zero_mem _
  · -- The residual lies in `W = range (extProj proj) = ⨅ i ∈ proj, ker (proj i)`.
    rw [extProj_range_eq_iInf_ker_proj, Submodule.mem_iInf]
    intro i
    rw [Submodule.mem_iInf]
    intro hi
    rw [LinearMap.mem_ker, LinearMap.proj_apply]
    -- A body of `proj` is either `r` (where the residual is `S r − S r = 0`) or outside `V(G)`
    -- (where it is `0` by the `else` branch), since `V(G) ∩ proj = {r}`.
    by_cases hiV : i ∈ F.graph.vertexSet
    · rw [if_pos hiV]
      have : i = r := (Set.ext_iff.1 hinter i).1 ⟨hiV, hi⟩ |>.symm ▸ rfl
      rw [this, sub_self]
    · rw [if_neg hiV]
  · -- `z + residual = S` pointwise.
    funext a
    by_cases haV : a ∈ F.graph.vertexSet
    · simp only [Pi.add_apply, if_pos haV, add_sub_cancel]
    · simp only [Pi.add_apply, if_neg haV, add_zero]

/-- **The exterior-column projection is injective on the rigidity-row span — at ANY rank, no
rigidity** (`lem:rigidityRows-splice-rank-add`, the L5a `hInj` injectivity; Katoh–Tanigawa 2011
§6.2 eq. (6.5) / Lemma 5.1, Phase 22i L5a-ii). The **deficiency-tolerant** sibling of
`BodyHingeFramework.injOn_extProj_dualMap_rigidityRows`: for *any* body-hinge framework `F` and a
block `proj` meeting `V(G)` in exactly the representative body `r`, the exterior-column projection's
dual map `D = (extProj proj).dualMap` is **injective on the rigidity-row span** `Φ = span
rigidityRows`. The chain is the *identical* dual-API computation as the rigid sibling
(`ker D = W.dualAnnihilator`, `Φ = Z.dualAnnihilator`, so `Φ ⊓ ker D = (Z ⊔ W).dualAnnihilator =
⊥`), differing only in the `Z ⊔ W = ⊤` input: here the rigidity-free
`infinitesimalMotions_sup_range_extProj_eq_top_of_inter_eq_singleton` rather than the rigid count.
This is the projection-loses-zero-rank fact at a *deficient* contraction leg, which the landed
rigidity-gated version cannot supply. -/
theorem BodyHingeFramework.injOn_extProj_dualMap_rigidityRows_of_inter_eq_singleton
    [Finite α] (F : BodyHingeFramework k α β) {proj : Set α} {r : α}
    (hinter : F.graph.vertexSet ∩ proj = {r}) :
    Set.InjOn (extProj (k := k) proj).dualMap (Submodule.span ℝ F.rigidityRows) := by
  classical
  haveI : Fintype α := Fintype.ofFinite α
  have hΦeq : Submodule.span ℝ F.rigidityRows
      = F.infinitesimalMotions.dualAnnihilator := by
    rw [F.infinitesimalMotions_eq_dualCoannihilator,
      Subspace.dualCoannihilator_dualAnnihilator_eq]
  refine LinearMap.injOn_of_disjoint_ker le_rfl ?_
  rw [disjoint_iff, LinearMap.ker_dualMap_eq_dualAnnihilator_range, hΦeq,
    ← Submodule.dualAnnihilator_sup_eq,
    infinitesimalMotions_sup_range_extProj_eq_top_of_inter_eq_singleton F hinter,
    Submodule.dualAnnihilator_top]

/-- **The exterior-column projection preserves the rigidity-row-span rank — at ANY rank, no
rigidity** (`lem:rigidityRows-splice-rank-add`, the L5a brick's `hInj` interface hypothesis;
Katoh–Tanigawa 2011 §6.2 eq. (6.5) / Lemma 5.1, Phase 22i L5a-ii). The direct `hInj`-form of the
column-deletion rank invariance: for *any* body-hinge framework `F` and a block `proj` meeting
`V(G)` in exactly the representative body `r`, the dual map `D = (extProj proj).dualMap` carries the
rigidity-row span `Sc = span rigidityRows` to an image of the **same** dimension,

  `finrank Sc = finrank (Sc.map D)`.

This is exactly the `hInj` hypothesis of `BodyHingeFramework.le_finrank_span_rigidityRows_of_splice`
(the L5a-i splice brick), discharged at a *deficient* contraction leg where the rigidity-gated route
is unavailable. It is the genuinely-new linear algebra of L5: deleting the single shared body `r`'s
columns preserves rank (KT Lemma 5.1, here as injectivity on `Sc` via
`injOn_extProj_dualMap_rigidityRows_of_inter_eq_singleton`), so the surviving block keeps its full
rank `D(|sc|−1) − k`. Immediate from injectivity on `Sc`
(`injOn_extProj_dualMap_rigidityRows_of_inter_eq_singleton`) via rank-nullity for the restricted
map. -/
theorem BodyHingeFramework.finrank_span_rigidityRows_map_extProj_dualMap_of_inter_eq_singleton
    [Finite α] (F : BodyHingeFramework k α β) {proj : Set α} {r : α}
    (hinter : F.graph.vertexSet ∩ proj = {r}) :
    Module.finrank ℝ ↥(Submodule.span ℝ F.rigidityRows) =
      Module.finrank ℝ
        ↥((Submodule.span ℝ F.rigidityRows).map (extProj (k := k) proj).dualMap) := by
  haveI : Fintype α := Fintype.ofFinite α
  set Sc := Submodule.span ℝ F.rigidityRows with hSc_def
  set D := (extProj (k := k) proj).dualMap with hD_def
  -- Injectivity on `Sc` is `Sc ⊓ ker D = ⊥`; rank-nullity for `D|Sc` then gives the equality.
  have hdisj : Sc ⊓ LinearMap.ker D = ⊥ :=
    disjoint_iff.mp (LinearMap.disjoint_ker_iff_injOn.mpr
      (F.injOn_extProj_dualMap_rigidityRows_of_inter_eq_singleton hinter))
  -- Rank-nullity for `D` restricted to `Sc`: `finrank (Sc.map D) + finrank (Sc ⊓ ker D)`
  -- `= finrank Sc`, and the kernel term is `0` by `hdisj`.
  letI hScAG : AddCommGroup ↥Sc := Sc.addCommGroup
  have hq : Module.finrank ℝ (↥Sc ⧸ (D.domRestrict Sc).ker) +
      Module.finrank ℝ ↥(D.domRestrict Sc).ker = Module.finrank ℝ ↥Sc :=
    (D.domRestrict Sc).ker.finrank_quotient_add_finrank
  have heq : Module.finrank ℝ (↥Sc ⧸ (D.domRestrict Sc).ker) =
      Module.finrank ℝ ↥(Sc.map D) := by
    have h := LinearEquiv.finrank_eq (D.domRestrict Sc).quotKerEquivRange
    rwa [LinearMap.range_domRestrict] at h
  have hker0 : Module.finrank ℝ ↥(D.domRestrict Sc).ker = 0 := by
    rw [LinearMap.ker_domRestrict,
      ← Submodule.finrank_map_subtype_eq Sc (Submodule.comap Sc.subtype (LinearMap.ker D)),
      Submodule.map_comap_subtype, hdisj, finrank_bot]
  rw [heq, hker0, add_zero] at hq
  exact hq.symm

/-- **The projected-subfamily extraction: a framework rigid on its full vertex set, pinned at a
block meeting `V(G)` in one body, carries `≥ D(|V(G)|−1)` independent *exterior-projected* panel
rows of its linking edges** (`lem:claim-6-4`, the U3b projected U3-tool skeleton — the
projected sibling of `exists_independent_panelRow_subfamily_of_rigidOn_linking_set`; Katoh–Tanigawa
2011 §6.2 eqs.\ (6.5)/(6.9), §5.1, Phase 22b — KT Claim 6.4 proper). For `F` infinitesimally rigid
on its whole vertex set `V(G)` and a block `proj` meeting `V(G)` in exactly the representative body
`r` (`V(G) ∩ proj = {r}`), there is an index subset `t` whose `(extProj proj).dualMap ∘ panelRow
ends`-subfamily is linearly independent, of size `≥ D(|V(G)|−1)`, every member of which links in
`F.graph`.

Unlike the un-projected parent — whose finrank bound the projection could in principle *lower* (that
is exactly the content of Claim 6.4) — this brick uses the §1.22 `Z ⊔ W = ⊤` injectivity input
(`injOn_extProj_dualMap_rigidityRows`): the exterior-column projection's dual map `D` is injective
on the rigidity-row span `Φ` (the projection loses *zero* rank), so the un-projected independent
subfamily of the green tool maps through `D` to an independent projected subfamily of the *same*
size (`LinearIndependent.map_injOn`). The un-projected subfamily and its support/count are produced
by `exists_independent_panelRow_subfamily_of_rigidOn_linking` (the equality-count form, whose
`Nat.card t = D(|V(G)|−1)` gives the `≥` lower bound directly); each of its panel rows is a rigidity
row of `F` (its edge links), so its span lies in `Φ` where `D` is injective. This is the final brick
of the exterior-rank discharge that the rank-transport `htransport` consumes. -/
theorem BodyHingeFramework.exists_independent_panelRow_subfamily_of_rigidOn_linking_set_proj
    [Finite α] [Finite β] (F : BodyHingeFramework k α β) {ends : β → α × α} {proj : Set α} {r : α}
    (hends : ∀ e u v, F.graph.IsLink e u v → F.graph.IsLink e (ends e).1 (ends e).2)
    (hne : ∀ e, F.graph.IsLink e (ends e).1 (ends e).2 → F.supportExtensor e ≠ 0)
    (hnev : F.graph.vertexSet.Nonempty)
    (hrig : F.IsInfinitesimallyRigidOn F.graph.vertexSet)
    (hr : r ∈ F.graph.vertexSet) (hinter : F.graph.vertexSet ∩ proj = {r}) :
    ∃ t : Set (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k),
      (∀ i ∈ t, F.graph.IsLink (i : β × _ × _).1 (ends (i : β × _ × _).1).1
        (ends (i : β × _ × _).1).2) ∧
      screwDim k * (F.graph.vertexSet.ncard - 1) ≤ Nat.card t ∧
      LinearIndependent ℝ (fun i : t => (extProj (k := k) proj).dualMap
        (F.panelRow ends (i : β × _ × _))) := by
  classical
  -- The un-projected independent subfamily from the green tool.
  obtain ⟨t, hsupp, hcard, hindep⟩ :=
    F.exists_independent_panelRow_subfamily_of_rigidOn_linking hends hne hnev hrig
  refine ⟨t, hsupp, hcard.ge, ?_⟩
  -- A panel row of `F` whose edge links in `F.graph` is one of `F`'s rigidity rows, so the
  -- subfamily's span lies in `Φ = span rigidityRows`, where `D` is injective (the §1.22 core).
  have hrow_mem : ∀ i : t,
      F.panelRow ends (i : β × _ × _) ∈ Submodule.span ℝ F.rigidityRows := by
    rintro ⟨⟨e', t₁, t₂⟩, hi⟩
    refine Submodule.subset_span ⟨e', (ends e').1, (ends e').2, hsupp _ hi,
      annihRow (F.supportExtensor e') t₁ t₂, ?_, rfl⟩
    rw [BodyHingeFramework.hingeRowBlock_apply, Submodule.mem_dualAnnihilator]
    intro x hx
    rw [Submodule.mem_span_singleton] at hx
    obtain ⟨ρ, rfl⟩ := hx
    rw [map_smul, annihRow_apply_self, smul_zero]
  have hspan_le : Submodule.span ℝ (Set.range (fun i : t => F.panelRow ends (i : β × _ × _)))
      ≤ Submodule.span ℝ F.rigidityRows :=
    Submodule.span_le.2 (fun _ ⟨i, hi⟩ => hi ▸ hrow_mem i)
  have hinj := F.injOn_extProj_dualMap_rigidityRows hrig hr hinter
  exact hindep.map_injOn _ (hinj.mono hspan_le)

/-- **Deficiency-aware exterior-projected independent surviving subfamily** (the V6-b leaf,
route-1 extractor; the `_le_finrank` analogue of
`exists_independent_panelRow_subfamily_of_rigidOn_linking_set_proj`, swapping the rigidity gate for
a rank input + the rigidity-free `injOn` core; Katoh–Tanigawa 2011 §6.2 eqs. (6.5)/(6.9),
Phase 22i L5b-ii-a). For a body-hinge framework `F` with a block `proj` meeting `V(G)` in exactly
the representative body `r` (`V(G) ∩ proj = {r}`), and given any rank lower bound `N ≤ finrank
(span F.rigidityRows)`, there is an index subset `t` whose
`(extProj proj).dualMap ∘ panelRow ends`-subfamily is linearly independent, of size `≥ N`, every
member of which links in `F.graph`.

This is the deficiency-aware twin of
`exists_independent_panelRow_subfamily_of_rigidOn_linking_set_proj` (route 1 of §1.66): instead of
deriving the un-projected subfamily from rigidity, it feeds the rank input `N` to the rank-input
extractor `exists_independent_panelRow_subfamily_of_le_finrank` (W6e), then maps the result through
the rigidity-free `injOn_extProj_dualMap_rigidityRows_of_inter_eq_singleton` (L5a-ii). The proof
body is the rigid extractor's proof verbatim with the two rigidity-gated calls swapped out. -/
theorem BodyHingeFramework.exists_independent_panelRow_subfamily_of_le_finrank_proj
    [Finite α] [Finite β] (F : BodyHingeFramework k α β) {ends : β → α × α} {proj : Set α} {r : α}
    (hends : ∀ e u v, F.graph.IsLink e u v → F.graph.IsLink e (ends e).1 (ends e).2)
    (hne : ∀ e, F.graph.IsLink e (ends e).1 (ends e).2 → F.supportExtensor e ≠ 0)
    (hinter : F.graph.vertexSet ∩ proj = {r})
    {N : ℕ} (hN : N ≤ Module.finrank ℝ (Submodule.span ℝ F.rigidityRows)) :
    ∃ t : Set (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k),
      (∀ i ∈ t, F.graph.IsLink (i : β × _ × _).1 (ends (i : β × _ × _).1).1
        (ends (i : β × _ × _).1).2) ∧
      N ≤ Nat.card t ∧
      LinearIndependent ℝ (fun i : t => (extProj (k := k) proj).dualMap
        (F.panelRow ends (i : β × _ × _))) := by
  classical
  -- The un-projected independent subfamily from the rank-input tool (W6e).
  obtain ⟨t, hsupp, hcard, hindep⟩ :=
    F.exists_independent_panelRow_subfamily_of_le_finrank hends hne hN
  refine ⟨t, hsupp, hcard.ge, ?_⟩
  -- A panel row of `F` whose edge links in `F.graph` is one of `F`'s rigidity rows, so the
  -- subfamily's span lies in `Φ = span rigidityRows`, where `D` is injective (the §1.22 core).
  have hrow_mem : ∀ i : t,
      F.panelRow ends (i : β × _ × _) ∈ Submodule.span ℝ F.rigidityRows := by
    rintro ⟨⟨e', t₁, t₂⟩, hi⟩
    refine Submodule.subset_span ⟨e', (ends e').1, (ends e').2, hsupp _ hi,
      annihRow (F.supportExtensor e') t₁ t₂, ?_, rfl⟩
    rw [BodyHingeFramework.hingeRowBlock_apply, Submodule.mem_dualAnnihilator]
    intro x hx
    rw [Submodule.mem_span_singleton] at hx
    obtain ⟨ρ, rfl⟩ := hx
    rw [map_smul, annihRow_apply_self, smul_zero]
  have hspan_le : Submodule.span ℝ (Set.range (fun i : t => F.panelRow ends (i : β × _ × _)))
      ≤ Submodule.span ℝ F.rigidityRows :=
    Submodule.span_le.2 (fun _ ⟨i, hi⟩ => hi ▸ hrow_mem i)
  -- The rigidity-free `injOn` core (L5a-ii): no rigidity hypothesis needed.
  have hinj := F.injOn_extProj_dualMap_rigidityRows_of_inter_eq_singleton hinter
  exact hindep.map_injOn _ (hinj.mono hspan_le)

/-- **The relabelled selector records the relabelled graph's links** (`lem:claim-6-4`, the U3a
contraction-leg `IsLink.map`-under-collapse fact; Katoh–Tanigawa 2011 §6.2, eq. (6.7), Phase 22b
route (i), risk (c)). If a parent endpoint selector `ends` records every link of `Gc` up to swap
(the edge-restricted `hends`, the form every fresh producer carries), then the *relabelled*
selector `endsᵐ e := (f (ends e).1, f (ends e).2)` records every link of the relabelled graph
`Gc.map f` up to swap.

This is the contracted-side analogue of `recordsLinks_swap_endsOf` for the contraction leg: a link
of `Gc.map f` is, by `Graph.map_isLink`, the `f`-image of a `Gc`-link `Gc.IsLink e x y` with
`f x = u`, `f y = v`; `ends` records *that* `Gc`-link (`hends`), and two `IsLink`s of the same edge
pin the same unordered pair (`IsLink.eq_and_eq_or_eq_and_eq`), so `(ends e).1, (ends e).2` is `x, y`
up to order; applying `f` gives `endsᵐ e = (u, v)` up to swap. This is the link-recording the U3a
swap-transport needs of the relabel selector `endsᵐ` (so that, against the IH realization's own
link-recording `Q.ends`, the two agree up to swap and the rigidity transports). -/
theorem PanelHingeFramework.recordsLinks_map_of_records
    {Gc : Graph α β} (f : α → α) (ends : β → α × α)
    (hends : ∀ e u v, Gc.IsLink e u v → Gc.IsLink e (ends e).1 (ends e).2) :
    ∀ e u v, (Gc.map f).IsLink e u v →
      ((f (ends e).1) = u ∧ (f (ends e).2) = v) ∨
      ((f (ends e).1) = v ∧ (f (ends e).2) = u) := by
  intro e u v he
  rw [Graph.map_isLink] at he
  obtain ⟨x, y, hxy, hfx, hfy⟩ := he
  rcases (hends e x y hxy).eq_and_eq_or_eq_and_eq hxy with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨by rw [h1, hfx], by rw [h2, hfy]⟩
  · exact Or.inr ⟨by rw [h1, hfy], by rw [h2, hfx]⟩

/-- **Two selectors recording the same graph's links agree up to swap** (`lem:claim-6-4`, the U3a
swap-bookkeeping infra; Katoh–Tanigawa 2011 §6.2, Phase 22b route (i)). If both `ends₁` and `ends₂`
record every link of `G` up to swap (the strengthened-motive link-recording conjunct's shape), then
on every link of `G` they agree up to swap. Both pin the *same* unordered pair on each link, so the
four cases of the two disjunctions collapse pairwise into the swap disjunction. This is the
selector-agnostic generalization of `recordsLinks_swap_endsOf` (which fixed `ends₂ = G.endsOf`); the
U3a transport feeds it the IH realization's own link-recording `Q.ends` (`hrec₁`) and the relabel
selector `endsᵐ`'s link-recording (`hrec₂`, from `recordsLinks_map_of_records`). -/
theorem PanelHingeFramework.recordsLinks_agree_swap
    {G : Graph α β} (ends₁ ends₂ : β → α × α)
    (hrec₁ : ∀ e u v, G.IsLink e u v →
      ((ends₁ e).1 = u ∧ (ends₁ e).2 = v) ∨ ((ends₁ e).1 = v ∧ (ends₁ e).2 = u))
    (hrec₂ : ∀ e u v, G.IsLink e u v →
      ((ends₂ e).1 = u ∧ (ends₂ e).2 = v) ∨ ((ends₂ e).1 = v ∧ (ends₂ e).2 = u)) :
    ∀ e u v, G.IsLink e u v →
      ((ends₁ e).1 = (ends₂ e).1 ∧ (ends₁ e).2 = (ends₂ e).2) ∨
      ((ends₁ e).1 = (ends₂ e).2 ∧ (ends₁ e).2 = (ends₂ e).1) := by
  intro e u v he
  rcases hrec₁ e u v he with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;>
    rcases hrec₂ e u v he with ⟨b1, b2⟩ | ⟨b1, b2⟩
  · exact Or.inl ⟨a1.trans b1.symm, a2.trans b2.symm⟩
  · exact Or.inr ⟨a1.trans b2.symm, a2.trans b1.symm⟩
  · exact Or.inr ⟨a1.trans b2.symm, a2.trans b1.symm⟩
  · exact Or.inl ⟨a1.trans b1.symm, a2.trans b2.symm⟩

/-- **The contraction leg's generic rigidity transports across the collapse map to the relabel
selector** (`lem:claim-6-4`, the U3a contraction-leg rigidity transport; Katoh–Tanigawa 2011 §6.2,
eqs. (6.7)/(6.9), Phase 22b route (i), design doc §1.20 U3a / §1.24 item 4 second half). Given the
contraction's *strengthened* generic IH `Qcf : HasGenericFullRankRealization k (Gc.map f)` (whose
witness `Q` carries the link-recording conjunct, so `Q.ends` records `Gc.map f`'s links), and a
parent selector `ends` recording `Gc`'s links (`hends`), produce a free-normal panel framework on
the relabelled graph `Gc.map f` at the **relabel selector**
`endsᵐ e := (f (ends e).1, f (ends e).2)`, in general position and infinitesimally rigid on its
whole vertex set `V(Gc.map f)`.

This is the contraction-leg face of the alignment §1.23 found undischarged in the bare motive — now
*derivable* from route (i)'s link-recording conjunct. The transport is the
`hasGenericRealization_transport_ends` pattern, against the relabel selector instead of the parent:
(1) `Q` is literally `ofNormals Q.graph Q.ends (Q.normal-pullback)`; the swap brick
`infinitesimalMotions_ofNormals_eq_of_ends_swap` carries its rigidity from `Q.ends` to `endsᵐ`,
since both record `Gc.map f`'s links and so agree up to swap (`recordsLinks_agree_swap` of
`Q.ends`'s own link-recording `hQrec` and the relabel selector's `recordsLinks_map_of_records`).
(2) General
position is a property of the normals alone (`ofNormals_normal`), unchanged by the selector, so the
relabel framework is again in general position. The output framework
`ofNormals (Gc.map f) endsᵐ nrm` is exactly the `Qcf'` the U3b projected-subfamily extraction
(`exists_independent_panelRow_subfamily_of_rigidOn_linking_set_proj`) consumes (a framework rigid on
its vertex set at a link-recording selector); U4 then carries the projected independence back to the
*uncollapsed* rows at the degenerate placement via the U2 row reproduction. -/
theorem PanelHingeFramework.hasGenericRealization_transport_relabel
    [Finite α] (Gc : Graph α β) (f : α → α) (ends : β → α × α)
    {n : ℕ} (hne : V(Gc.map f).Nonempty) (hdef : (Gc.map f).deficiency n = 0)
    (Qcf : PanelHingeFramework.HasGenericFullRankRealization k n (Gc.map f))
    (hends : ∀ e u v, Gc.IsLink e u v → Gc.IsLink e (ends e).1 (ends e).2) :
    ∃ nrm : α × Fin (k + 2) → ℝ,
      (PanelHingeFramework.ofNormals (Gc.map f)
        (fun e => (f (ends e).1, f (ends e).2)) nrm).IsGeneralPosition ∧
      (PanelHingeFramework.ofNormals (Gc.map f)
        (fun e => (f (ends e).1, f (ends e).2)) nrm).toBodyHinge.IsInfinitesimallyRigidOn
        V(Gc.map f) := by
  obtain ⟨Q, hQg, hQgp, hQrank, hQrec, _⟩ := Qcf
  -- Derive rigidity from hQrank via B1.mpr.
  have hne' : Q.toBodyHinge.graph.vertexSet.Nonempty := by
    rw [PanelHingeFramework.toBodyHinge_graph, hQg]; exact hne
  rw [hdef, sub_zero] at hQrank
  have hVeq : V(Gc.map f) = Q.toBodyHinge.graph.vertexSet := by
    rw [PanelHingeFramework.toBodyHinge_graph, hQg]
  have h1 : 1 ≤ V(Gc.map f).ncard := (Set.ncard_pos (Set.toFinite _)).2 hne
  have hQrig : Q.toBodyHinge.IsInfinitesimallyRigidOn V(Gc.map f) := by
    rw [hVeq, BodyHingeFramework.isInfinitesimallyRigidOn_vertexSet_iff_finrank_span_rigidityRows
        Q.toBodyHinge hne', ← hVeq]
    zify [h1] at hQrank ⊢; exact_mod_cast hQrank
  set endsM : β → α × α := fun e => (f (ends e).1, f (ends e).2) with hendsM
  set nrm := (fun p => Q.normal p.1 p.2 : α × Fin (k + 2) → ℝ) with hnrm
  -- General position transfers to `ofNormals … endsM …` verbatim (normals are `Q.normal`, unchanged
  -- by the selector); the graph-arg of `IsGeneralPosition` is irrelevant (it reads only normals).
  have hgp' : (PanelHingeFramework.ofNormals (Gc.map f) endsM nrm).IsGeneralPosition := by
    intro a b hab
    simpa only [hnrm, PanelHingeFramework.ofNormals_normal] using hQgp a b hab
  refine ⟨nrm, hgp', ?_⟩
  -- The two selectors `Q.ends` and `endsM := f ∘ (parent ends)` both record `Q.graph = Gc.map f`'s
  -- links (route (i)'s conjunct `hQrec` and the relabelled `recordsLinks_map_of_records`), so they
  -- agree up to swap; the swap brick then equates the motion spaces of `Q = ofNormals Q.graph
  -- Q.ends nrm` and `ofNormals Q.graph endsM nrm`.
  have hswap : ∀ e u v, Q.graph.IsLink e u v →
      ((Q.ends e).1 = (endsM e).1 ∧ (Q.ends e).2 = (endsM e).2) ∨
      ((Q.ends e).1 = (endsM e).2 ∧ (Q.ends e).2 = (endsM e).1) := by
    rw [hQg]
    exact PanelHingeFramework.recordsLinks_agree_swap Q.ends endsM hQrec
      (PanelHingeFramework.recordsLinks_map_of_records f ends hends)
  have hmot : (PanelHingeFramework.ofNormals Q.graph endsM nrm).toBodyHinge.infinitesimalMotions
      = (PanelHingeFramework.ofNormals Q.graph Q.ends nrm).toBodyHinge.infinitesimalMotions :=
    PanelHingeFramework.infinitesimalMotions_ofNormals_eq_of_ends_swap
      Q.graph endsM Q.ends nrm hswap
  -- Rigidity at `endsM`: rewrite the graph to `Q.graph` (in both the goal and the IH rigidity),
  -- then move rigidity off `Q` via `hmot`.
  rw [← hQg] at hQrig ⊢
  intro S hS u hu v hv
  refine hQrig S ?_ u hu v hv
  rw [← BodyHingeFramework.mem_infinitesimalMotions] at hS ⊢
  rw [hmot] at hS
  -- `Q = ofNormals Q.graph Q.ends nrm` definitionally (structure eta + `nrm = Q.normal`-pullback).
  exact hS

/-- **The contraction leg's rank transports across the collapse map to the relabel selector — at any
deficiency, no rigidity** (`lem:case-I-realization-all-k`, the V6-b deficiency-aware relabel
transport; Katoh–Tanigawa 2011 §6.2, eq. (6.5) / Lemma 5.1, Phase 22i L5b-i). The
**deficiency-tolerant** sibling of `hasGenericRealization_transport_relabel`: where the rigid
version converts the contraction's *full* rank to `IsInfinitesimallyRigidOn` and hands that to the
rigid projected-subfamily extractor, this carries the contraction's IH rank — the
**possibly-deficient** value `D(|V(Gc.map f)|−1) − def(Gc.map f)` — across the relabel selector swap
as a plain `finrank` equality, available at `def = k > 0` where the rigid route is not.

The transport is rigidity-free for the same reason the rigid one is: the relabel selector
`endsᵐ e := (f (ends e).1, f (ends e).2)` and the IH realization's own selector `Q.ends` record the
same unordered link of every edge of `Gc.map f` (`recordsLinks_agree_swap` of `Q`'s link-recording
conjunct `hQrec` and the relabelled `recordsLinks_map_of_records`), so the selector-swap brick
`infinitesimalMotions_ofNormals_eq_of_ends_swap` equates the motion spaces of `Q = ofNormals Q.graph
Q.ends nrm` and `ofNormals (Gc.map f) endsᵐ nrm`; equal motion spaces give equal rigidity-row spans
(`span_rigidityRows_eq_of_infinitesimalMotions_eq`), hence equal finrank. General position transfers
verbatim (a property of the normals alone). The output framework `ofNormals (Gc.map f) endsᵐ nrm` is
the relabel-leg framework the splice brick reads at the surviving block; its rank equals the
contraction IH's, so it inherits the deficient surviving rank `D(|sc|−1) − def` directly — the
shared core both candidate L5b-i routes need (the `_proj` mirror's transport step and the
pulled-back full-span route's seed-placement step). -/
theorem PanelHingeFramework.finrank_span_rigidityRows_ofNormals_relabel_eq
    [Finite α] (Gc : Graph α β) (f : α → α) (ends : β → α × α)
    {n : ℕ} (Qcf : PanelHingeFramework.HasGenericFullRankRealization k n (Gc.map f))
    (hends : ∀ e u v, Gc.IsLink e u v → Gc.IsLink e (ends e).1 (ends e).2) :
    ∃ nrm : α × Fin (k + 2) → ℝ,
      (PanelHingeFramework.ofNormals (Gc.map f)
        (fun e => (f (ends e).1, f (ends e).2)) nrm).IsGeneralPosition ∧
      (Module.finrank ℝ (Submodule.span ℝ
        (PanelHingeFramework.ofNormals (Gc.map f)
          (fun e => (f (ends e).1, f (ends e).2)) nrm).toBodyHinge.rigidityRows) : ℤ)
        = screwDim k * ((V(Gc.map f).ncard : ℤ) - 1) - (Gc.map f).deficiency n := by
  obtain ⟨Q, hQg, hQgp, hQrank, hQrec, _⟩ := Qcf
  set endsM : β → α × α := fun e => (f (ends e).1, f (ends e).2) with hendsM
  set nrm := (fun p => Q.normal p.1 p.2 : α × Fin (k + 2) → ℝ) with hnrm
  -- General position transfers to `ofNormals … endsM …` verbatim (the normals are `Q.normal`,
  -- unchanged by the selector; `IsGeneralPosition` reads only the normals).
  have hgp' : (PanelHingeFramework.ofNormals (Gc.map f) endsM nrm).IsGeneralPosition := by
    intro a b hab
    simpa only [hnrm, PanelHingeFramework.ofNormals_normal] using hQgp a b hab
  refine ⟨nrm, hgp', ?_⟩
  -- The two selectors `Q.ends` and `endsM := f ∘ (parent ends)` both record `Q.graph = Gc.map f`'s
  -- links, so they agree up to swap; the swap brick then equates the motion spaces of
  -- `Q = ofNormals Q.graph Q.ends nrm` and `ofNormals Q.graph endsM nrm`.
  have hswap : ∀ e u v, Q.graph.IsLink e u v →
      ((Q.ends e).1 = (endsM e).1 ∧ (Q.ends e).2 = (endsM e).2) ∨
      ((Q.ends e).1 = (endsM e).2 ∧ (Q.ends e).2 = (endsM e).1) := by
    rw [hQg]
    exact PanelHingeFramework.recordsLinks_agree_swap Q.ends endsM hQrec
      (PanelHingeFramework.recordsLinks_map_of_records f ends hends)
  have hmot : (PanelHingeFramework.ofNormals Q.graph endsM nrm).toBodyHinge.infinitesimalMotions
      = (PanelHingeFramework.ofNormals Q.graph Q.ends nrm).toBodyHinge.infinitesimalMotions :=
    PanelHingeFramework.infinitesimalMotions_ofNormals_eq_of_ends_swap
      Q.graph endsM Q.ends nrm hswap
  -- Equal motion spaces ⟹ equal rigidity-row spans ⟹ equal finrank. `Q = ofNormals Q.graph Q.ends
  -- nrm` definitionally (structure eta + `nrm = Q.normal`-pullback), and `Q.graph = Gc.map f`.
  have hspan : Submodule.span ℝ
      (PanelHingeFramework.ofNormals (Gc.map f) endsM nrm).toBodyHinge.rigidityRows
      = Submodule.span ℝ Q.toBodyHinge.rigidityRows := by
    rw [← hQg]
    exact BodyHingeFramework.span_rigidityRows_eq_of_infinitesimalMotions_eq _ _ hmot
  rw [hspan, hQrank]

/-- **Rank polynomial for the relabeled contraction leg — deficiency-aware** (Phase 22i L5b-i
completion, V6-b leaf via route 2; KT §6.2 eqs. (6.3)/(6.9)). From a generic full-rank
realization of the relabeled contraction `Gc.map f` (the IH at a possibly-deficient contraction),
a Loopless hypothesis on `Gc.map f`, and a parent link-recording selector `hends`, produces:
* a natural number `N` satisfying the ℤ-identity
  `(N : ℤ) = screwDim k * (|V(Gc.map f)| − 1) − def(Gc.map f, n)`;
* a nonzero rational polynomial `Q` such that at every `Q`-non-root seed `q`,
  `N ≤ finrank (span rigidityRows of ofNormals (Gc.map f) endsᵐ q)` where
  `endsᵐ e := (f (ends e).1, f (ends e).2)`.

This is the surviving-block rank input the splice brick needs at any fresh combined seed: combined
with the placement-free `hInj`
(`finrank_span_rigidityRows_map_extProj_dualMap_of_inter_eq_singleton`)
and the H-leg rigid polynomial, the splice brick `le_finrank_span_rigidityRows_of_splice` closes the
block-sum `≥` at any alg-indep seed that is a non-root of the product `Q_H · Q_c · Q_gp`.

Route 2: call the shared core `finrank_span_rigidityRows_ofNormals_relabel_eq` to obtain a witness
seed `nrm` where the finrank already equals `N`; supply this to the L4b-1 deficiency-aware rank
polynomial `exists_rankPolynomial_of_le_finrank_linking` with `hN := le_refl` (the rank bound at
`nrm` is exact). The `hne` (support extensor nonzero at `nrm`) comes from GP (transferred by the
shared core from `Qcf`) + `hloop` (looplessness of `Gc.map f` gives `(endsᵐ e).1 ≠ (endsᵐ e).2`
for every link `e` of `Gc.map f`). -/
theorem PanelHingeFramework.exists_rankPolynomial_of_IH_relabel_linking
    [Finite α] [Finite β] (Gc : Graph α β) (f : α → α) (ends : β → α × α)
    {n : ℕ} (hQcf : PanelHingeFramework.HasGenericFullRankRealization k n (Gc.map f))
    (hloop : (Gc.map f).Loopless)
    (hends : ∀ e u v, Gc.IsLink e u v → Gc.IsLink e (ends e).1 (ends e).2) :
    ∃ N : ℕ,
      (N : ℤ) = screwDim k * ((V(Gc.map f).ncard : ℤ) - 1) - (Gc.map f).deficiency n ∧
      ∃ Q : MvPolynomial (α × Fin (k + 2)) ℝ,
        Q ≠ 0 ∧ (Q.coeffs : Set ℝ) ⊆ Set.range (algebraMap ℚ ℝ) ∧
        ∀ q : α × Fin (k + 2) → ℝ, MvPolynomial.eval q Q ≠ 0 →
          N ≤ Module.finrank ℝ (Submodule.span ℝ
            (PanelHingeFramework.ofNormals (Gc.map f)
              (fun e => (f (ends e).1, f (ends e).2)) q).toBodyHinge.rigidityRows) := by
  -- Step 1: shared core — get witness seed `nrm` with GP and ℤ-rank equality.
  obtain ⟨nrm, hgp, hrank_eq⟩ :=
    PanelHingeFramework.finrank_span_rigidityRows_ofNormals_relabel_eq Gc f ends hQcf hends
  -- Let `N` be the finrank at `nrm`; the ℤ-equality from the shared core gives `(N : ℤ) = ...`.
  set endsM : β → α × α := fun e => (f (ends e).1, f (ends e).2)
  set N := Module.finrank ℝ (Submodule.span ℝ
    (PanelHingeFramework.ofNormals (Gc.map f) endsM nrm).toBodyHinge.rigidityRows) with hN_def
  refine ⟨N, ?_, ?_⟩
  · -- `(N : ℤ) = ...` from the shared core's ℤ-equality (which already has this form).
    exact_mod_cast hrank_eq
  -- Step 2: derive `hendsM_link` — `endsM` records `Gc.map f`'s links.
  -- `recordsLinks_map_of_records` gives a disjunction; we peel to the single-link form.
  have hendsM_link : ∀ e u v, (Gc.map f).IsLink e u v →
      (Gc.map f).IsLink e (endsM e).1 (endsM e).2 := by
    intro e u v he
    rcases PanelHingeFramework.recordsLinks_map_of_records f ends hends e u v he with
      ⟨h1, h2⟩ | ⟨h1, h2⟩
    · simp only [endsM, h1, h2]; exact he
    · simp only [endsM, h1, h2]; exact he.symm
  -- Step 3: `hne` — support extensor nonzero at `nrm` for every `Gc.map f`-link at `endsM`.
  have hne : ∀ e, (Gc.map f).IsLink e (endsM e).1 (endsM e).2 →
      (PanelHingeFramework.ofNormals (Gc.map f) endsM nrm).toBodyHinge.supportExtensor e ≠ 0 := by
    intro e he
    apply PanelHingeFramework.supportExtensor_ne_zero_of_isGeneralPosition _ hgp
    rw [PanelHingeFramework.ofNormals_ends]
    haveI : (Gc.map f).Loopless := hloop
    exact he.ne
  -- Step 4: apply the L4b-1 deficiency-aware rank polynomial at `nrm` with `hN := le_refl`.
  obtain ⟨Q, hQne, hQrat, hQtrans⟩ :=
    PanelHingeFramework.exists_rankPolynomial_of_le_finrank_linking
      (Gc.map f) endsM hendsM_link hne (le_refl N)
  exact ⟨Q, fun hQ0 => hQne (by rw [hQ0, map_zero]), hQrat, hQtrans⟩

/-- **Coordinate of `D w` as a matrix-vector product in a basis identification** (the linearity
fact behind the `D ∘ panelRow` coordinatization N-22b-2; standard linear algebra). For a finite-dim
ℝ-space `W` with a basis identification `φ : W ≃ₗ[ℝ] (Fin n → ℝ)` and any linear endomorphism `D`,
the `j`-th coordinate of `D w` is the matrix-vector product `∑ l, M j l · (φ w) l` where
`M j l = φ (D (φ⁻¹ eₗ)) j` is the matrix of `φ ∘ D ∘ φ⁻¹` in the standard basis. Stated generically
(not over the heavy `Module.Dual ℝ (α → ScrewSpace k)`) so the `map_sum`/`apply_symm_apply` chain
never triggers a `whnf` on the concrete dual type. -/
private theorem coord_linearMap_eq_matrix_mulVec {W : Type*} [AddCommGroup W] [Module ℝ W]
    {n : ℕ} (φ : W ≃ₗ[ℝ] (Fin n → ℝ)) (D : W →ₗ[ℝ] W) (w : W) (j : Fin n) :
    φ (D w) j = ∑ l, φ (D (φ.symm (Pi.single l 1))) j * φ w l := by
  -- The standard `Fin n → ℝ` basis decomposition of the coordinate vector `φ w`.
  have hbasis : (φ w) = ∑ l, (φ w l) • (Pi.single l 1 : Fin n → ℝ) := by
    funext m
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, Pi.single_apply, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq Finset.univ m (fun l => φ w l)]
    simp
  have hw : w = ∑ l, (φ w l) • φ.symm (Pi.single l 1) := by
    apply φ.injective
    rw [map_sum]
    simp only [map_smul, φ.apply_symm_apply]
    exact hbasis
  conv_lhs => rw [hw]
  rw [map_sum, map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_smul, map_smul, Pi.smul_apply, smul_eq_mul, mul_comm]

/-- **The matrix entry of `f.dualMap` in the dual-standard basis is `(b.dualBasis (e l)) (f (b (e
j)))`** (the linearity fact behind the N-22b-2 projected-coordinate rationality; standard linear
algebra). For a finite basis `b : Basis ι R W`, an index equiv `e : Fin n ≃ ι`, the dual-standard
basis identification `φ := b.dualBasis.equivFun ≪≫ₗ funCongrLeft R R e`, and any linear endomorphism
`f : W →ₗ[R] W`, the `(j, l)` entry of the matrix of `φ ∘ f.dualMap ∘ φ⁻¹` reads as evaluating the
dual basis functional `b.dualBasis (e l)` at `f (b (e j))`. Stated generically (not over the heavy
`Module.Dual ℝ (α → ScrewSpace k)`), so the `φ`/`dualBasis` unfolding never triggers a
`whnf`/`isDefEq` on the concrete dual type. For a `0`/`proj` projection `f = extProj proj` this
entry is a Kronecker `0`/`1`, hence rational — the input the projected rank polynomial's
rationality needs. -/
private theorem dualMap_matrix_entry_eq {ι R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]
    {n : ℕ} (b : Module.Basis ι R W) [Finite ι] [DecidableEq ι] (e : Fin n ≃ ι)
    (f : W →ₗ[R] W) (j l : Fin n) :
    (b.dualBasis.equivFun.trans (LinearEquiv.funCongrLeft R R e))
        (f.dualMap ((b.dualBasis.equivFun.trans (LinearEquiv.funCongrLeft R R e)).symm
          (Pi.single l 1))) j
      = b.dualBasis (e l) (f (b (e j))) := by
  classical
  haveI : Fintype ι := Fintype.ofFinite ι
  have hsymm : (b.dualBasis.equivFun.trans (LinearEquiv.funCongrLeft R R e)).symm (Pi.single l 1)
      = b.dualBasis (e l) := by
    rw [LinearEquiv.trans_symm, LinearEquiv.trans_apply, LinearEquiv.funCongrLeft_symm,
      LinearEquiv.funCongrLeft_apply, Module.Basis.equivFun_symm_apply, Finset.sum_eq_single (e l)]
    · rw [LinearMap.funLeft_apply, Equiv.symm_apply_apply, Pi.single_eq_same, one_smul]
    · intro b' _ hb'
      rw [LinearMap.funLeft_apply,
        Pi.single_eq_of_ne (by rw [ne_eq, e.symm_apply_eq]; exact hb'), zero_smul]
    · exact fun h => absurd (Finset.mem_univ _) h
  rw [LinearEquiv.trans_apply, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply,
    Module.Basis.dualBasis_equivFun, LinearMap.dualMap_apply, hsymm]

/-- **The `D ∘ panelRow` rank polynomial: a projected-independent subfamily at one placement yields
a nonzero rank polynomial witnessing exterior-projected row-independence at its generic locus**
(`lem:claim-6-4` packaging brick N-22b-2; Katoh–Tanigawa 2011 §5.1, §6.2 eqs. (6.5)/(6.9), Phase
22b). The **bounded packaging** half of the Claim-6.4 discharge: the projected sibling of
`exists_rankPolynomial_of_rigidOn_linking_set` whose row family is post-composed with the fixed
exterior-column projection `D := (extProj proj).dualMap`. Where the un-projected parent *derives*
its independent subfamily from `hrig` via the body-set N7b-0, this brick takes the
**already-projected independence at the witness placement `q₀`** as the hypothesis `hindep` — the
`∃`-one-placement output of the research-shaped rank-transport N-22b-1 (the contraction's generic IH
carried across the collapse map by algebraic independence) — and packages it into the `Qc`-non-root
form the block-triangular coupling consumes.

It re-instantiates the generic engine `exists_polynomial_ne_zero_of_linearIndependent_at` (fully
generic in its target space) at the **post-projection** family `g q i := D (panelRow ends i)`. Since
`D` is `q`-independent and linear, the coordinatization survives as the `D`-pullback of the parent's
panel polynomials: writing `M` for the matrix of `φ ∘ D ∘ φ⁻¹` in the dual-standard basis,
`φ (D (panelRow ends i)) j = ∑ l, M j l · φ (panelRow ends i) l = ∑ l, M j l · eval q (c i l)`, so
each projected coordinate is the polynomial `cD i j := ∑ l, C (M j l) · c i l`. The witnessed
subfamily index `t`, its linking-edge support `hsupp`, and the count `hscard` are passed through
unchanged. **No new matrix-rank theory** (the engine is generic in `W`; here
`W = Module.Dual ℝ (α → ScrewSpace k)` is the same finite-dim dual as the parent). The output is the
conjunct `hclaim64` of `case_I_realization` consumes, modulo the rank-transport supplying `t`. -/
theorem PanelHingeFramework.exists_rankPolynomial_of_rigidOn_linking_set_proj [Finite α] [Finite β]
    (G : Graph α β) (ends : β → α × α) (proj : Set α) {m : ℕ}
    {q₀ : α × Fin (k + 2) → ℝ}
    {t : Set (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k)}
    (hsupp : ∀ i ∈ t, G.IsLink (i : β × _ × _).1 (ends (i : β × _ × _).1).1
      (ends (i : β × _ × _).1).2)
    (hcount : m ≤ Nat.card t)
    (hindep : LinearIndependent ℝ (fun i : t => (extProj (k := k) proj).dualMap
      ((PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.panelRow ends (i : β × _ × _)))) :
    ∃ Qc : MvPolynomial (α × Fin (k + 2)) ℝ, Qc ≠ 0 ∧
      (Qc.coeffs : Set ℝ) ⊆ Set.range (algebraMap ℚ ℝ) ∧
      ∀ q : α × Fin (k + 2) → ℝ, MvPolynomial.eval q Qc ≠ 0 →
        ∃ rsc : Set (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k),
          (∀ i ∈ rsc, G.IsLink (i : β × _ × _).1 (ends (i : β × _ × _).1).1
            (ends (i : β × _ × _).1).2) ∧ m ≤ Nat.card rsc ∧
          LinearIndependent ℝ (fun i : rsc => (extProj (k := k) proj).dualMap
            ((PanelHingeFramework.ofNormals G ends q).toBodyHinge.panelRow ends
              (i : β × _ × _))) := by
  classical
  haveI : Fintype α := Fintype.ofFinite α
  set D := (extProj (k := k) proj).dualMap with hDdef
  -- The standard basis of `α → ScrewSpace k`, its dual-basis identification `φ`, and the bridge to
  -- the canonical `Fin (finrank …)` index that the engine's `c`/`φ` require (verbatim the parent).
  set B : Module.Basis (Σ _ : α, Set.powersetCard (Fin (k + 2)) k) ℝ (α → ScrewSpace k) :=
    Pi.basis (fun _ : α => screwBasis k) with hB
  have hcardB : Fintype.card (Σ _ : α, Set.powersetCard (Fin (k + 2)) k)
      = Module.finrank ℝ (Module.Dual ℝ (α → ScrewSpace k)) := by
    rw [Subspace.dual_finrank_eq, Module.finrank_eq_card_basis B]
  let e : Fin (Module.finrank ℝ (Module.Dual ℝ (α → ScrewSpace k)))
      ≃ (Σ _ : α, Set.powersetCard (Fin (k + 2)) k) :=
    (Fintype.equivFinOfCardEq hcardB).symm
  set φ : Module.Dual ℝ (α → ScrewSpace k)
      ≃ₗ[ℝ] (Fin (Module.finrank ℝ (Module.Dual ℝ (α → ScrewSpace k))) → ℝ) :=
    B.dualBasis.equivFun.trans (LinearEquiv.funCongrLeft ℝ ℝ e) with hφ
  -- The parent panel-row family + its degree-2 panel-polynomial coordinates, pulled back along `e`.
  set g : (α × Fin (k + 2) → ℝ)
      → (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k)
      → Module.Dual ℝ (α → ScrewSpace k) :=
    fun q i => (PanelHingeFramework.ofNormals G ends q).toBodyHinge.panelRow ends i with hg_def
  set c : (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k)
      → Fin (Module.finrank ℝ (Module.Dual ℝ (α → ScrewSpace k)))
      → MvPolynomial (α × Fin (k + 2)) ℝ :=
    fun i j => ((if (ends i.1).1 = (e j).1 then (1 : ℝ) else 0)
        - (if (ends i.1).2 = (e j).1 then 1 else 0))
      • annihRowPoly (ends i.1).1 (ends i.1).2 i.2.1 i.2.2 (e j).2 with hc_def
  -- The parent evaluation identity: each panel-row coordinate is the panel polynomial `c`.
  have hg : ∀ q i j, φ (g q i) j = MvPolynomial.eval q (c i j) := by
    intro q i j
    rw [hφ, LinearEquiv.trans_apply, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply,
      Module.Basis.dualBasis_equivFun, hg_def, hc_def]
    rcases hej : e j with ⟨a, t'⟩
    simp only [hej]
    simp only [hB, Pi.basis_apply]
    change BodyHingeFramework.panelRow _ ends i (Pi.single a (screwBasis k t')) = _
    rw [BodyHingeFramework.panelRow, BodyHingeFramework.hingeRow_apply,
      PanelHingeFramework.toBodyHinge_supportExtensor,
      PanelHingeFramework.ofNormals_ends, PanelHingeFramework.ofNormals_normal,
      PanelHingeFramework.ofNormals_normal, MvPolynomial.smul_eval, annihRowPoly_eval]
    rw [Pi.single_apply, Pi.single_apply]
    by_cases hu : (ends i.1).1 = a <;> by_cases hv : (ends i.1).2 = a <;>
      simp only [hu, hv, if_true, if_false, sub_zero, zero_sub, sub_self, map_zero,
        map_neg, one_mul, neg_mul, zero_mul]
  -- The matrix `M` of `φ ∘ D ∘ φ⁻¹` in the dual-standard basis: `M j l = φ (D (φ⁻¹ (eₗ))) j`.
  set M : Fin (Module.finrank ℝ (Module.Dual ℝ (α → ScrewSpace k)))
      → Fin (Module.finrank ℝ (Module.Dual ℝ (α → ScrewSpace k))) → ℝ :=
    fun j l => φ (D (φ.symm (Pi.single l 1))) j with hM_def
  -- The projected family `gD q i := D (panelRow ends i)`, coordinates `cD := M-pullback of c`.
  set gD : (α × Fin (k + 2) → ℝ)
      → (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k)
      → Module.Dual ℝ (α → ScrewSpace k) := fun q i => D (g q i) with hgD_def
  set cD : (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k)
      → Fin (Module.finrank ℝ (Module.Dual ℝ (α → ScrewSpace k)))
      → MvPolynomial (α × Fin (k + 2)) ℝ :=
    fun i j => ∑ l, MvPolynomial.C (M j l) * c i l with hcD_def
  -- The matrix identity `φ (D w) j = ∑ l, M j l * φ w l`, via the generic linearity helper (stated
  -- away from the heavy dual type, so no `whnf` on the concrete dual is triggered).
  have hMrep : ∀ (w : Module.Dual ℝ (α → ScrewSpace k)) j,
      φ (D w) j = ∑ l, M j l * φ w l :=
    fun w j => by rw [hM_def]; exact coord_linearMap_eq_matrix_mulVec φ D w j
  -- Each matrix entry `M j l` is `0` or `1` (`extProj` is a `0`/`proj` projection in the
  -- dual-standard basis), hence rational. The entry reads
  -- `M j l = (B.dualBasis (e l)) (extProj proj (B (e j)))`, and `extProj proj (B (e j))` is `0`
  -- (when `(e j).1 ∈ proj`) or the standard basis vector `B (e j)` itself, on which the dual basis
  -- is the Kronecker delta `0`/`1`.
  have hMrat : ∀ j l, M j l ∈ Set.range (algebraMap ℚ ℝ) := by
    intro j l
    -- `M j l = B.dualBasis (e l) (extProj proj (B (e j)))` (the dual-map matrix entry, via the
    -- generic helper that never `whnf`s the concrete dual type) — a Kronecker `0`/`1` against the
    -- `0`/`proj` projection of a standard basis vector, hence rational.
    have hval : M j l = B.dualBasis (e l) (extProj (k := k) proj (B (e j))) := by
      rw [hM_def, hφ, hDdef]; exact dualMap_matrix_entry_eq B e (extProj proj) j l
    rw [hval]
    -- `extProj proj (B (e j))` is `0` (when `(e j).1 ∈ proj`) or `B (e j)` itself.
    by_cases ha : (e j).1 ∈ proj
    · have hz : extProj (k := k) proj (B (e j)) = 0 := by
        funext b
        rw [Pi.zero_apply]
        by_cases hb : b ∈ proj
        · exact extProj_apply_mem hb _
        · rw [extProj_apply_not_mem hb, hB, Pi.basis_apply, Pi.single_eq_of_ne
            (by rintro rfl; exact hb ha)]
      rw [hz, map_zero]; exact ⟨0, map_zero _⟩
    · have hid : extProj (k := k) proj (B (e j)) = B (e j) := by
        funext b
        by_cases hb : b ∈ proj
        · rw [extProj_apply_mem hb, hB, Pi.basis_apply,
            Pi.single_eq_of_ne (by rintro rfl; exact ha hb)]
        · rw [extProj_apply_not_mem hb]
      rw [hid, Module.Basis.dualBasis_apply_self]
      exact ⟨if e j = e l then 1 else 0, by split_ifs <;> simp⟩
  -- The projected coordinate `cD i j = ∑ l, C(M j l) · c i l` is rational: `M j l` rational
  -- (above), `c i l` rational (the parent panel polynomial), `range` closed under `C(·)·`, sums.
  have hcD : ∀ i j, cD i j ∈ (MvPolynomial.map (algebraMap ℚ ℝ) (σ := α × Fin (k + 2))).range := by
    intro i j
    rw [hcD_def]
    refine Subring.sum_mem _ fun l _ => Subring.mul_mem _ ?_ ?_
    · obtain ⟨r, hr⟩ := hMrat j l
      exact ⟨MvPolynomial.C r, by rw [MvPolynomial.map_C, hr]⟩
    · rw [hc_def]; exact annihRowPoly_smul_sign_mem_range_map _ _ _ _ _ _
  -- The projected evaluation identity: each projected coordinate is the polynomial `cD`.
  have hgD : ∀ q i j, φ (gD q i) j = MvPolynomial.eval q (cD i j) := by
    intro q i j
    rw [hgD_def, hMrep, hcD_def, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_mul, MvPolynomial.eval_C, hg]
  -- Extract the *rational* witnessing rank polynomial via the engine on the projected family.
  obtain ⟨Q, hQ₀, hQrat, hQ⟩ :=
    exists_polynomial_ne_zero_of_linearIndependent_at_coeffs_subset_range gD cD φ hgD hcD
      (p₀ := q₀) (s := t) (by simpa only [hgD_def, hg_def, hDdef] using hindep)
  refine ⟨Q, fun hQz => hQ₀ (by rw [hQz, map_zero]), hQrat, fun q hq => ?_⟩
  exact ⟨t, hsupp, hcount, by simpa only [hgD_def, hg_def, hDdef] using hQ q hq⟩

/-- **KT Claim 6.4 — the contraction leg's rank transports across the collapse map to a
single-placement exterior-projected surviving-row witness** (`lem:claim-6-4`, the N-22b-1
rank-transport; Katoh–Tanigawa 2011 §6.2/§5.1, eqs.\ (6.5)/(6.9), Phase 22b).

This is the genuinely-new analytic content of Case I — the one obligation Phase 22a left
green-modulo (the composer `case_I_realization`'s `hclaim64` reduces to *this* witness followed by
the bounded packaging `exists_rankPolynomial_of_rigidOn_linking_set_proj`, N-22b-2). KT's eq. (6.3)
block decomposition of `R(G,p)` puts the rigid block `H` in one block and the parent **restricted to
the surviving edges** `R(G,p; E∖E′, V∖V′)` in the other; the surviving-edge subgraph is
`G.deleteEdges E(H)` (a *literal* `≤ G` subgraph, `edgeSet_rigidContract`), and the collapse to the
representative body `v∗ = r` lives entirely on the *placement* side (eq. (6.7)'s `p_{E∖E′}`).

KT **Claim 6.4** (eq. (6.9)) is the rank-transport `rank R(G/E′, p_{E∖E′}) ≥ rank R(G/E′, p2)`:
because the joint panel coefficients are algebraically independent over ℚ (general position — the GP
conjunct of the contraction's *generic* IH), the `p_{E∖E′}`-realization of `G ＼ E(H)` attains the
contraction's rank, **restricted to the surviving body columns** `V∖V′ = V(G)∖V(H)` (the
exterior-column projection `D = (extProj V(H)).dualMap`). In the project's exterior-projected
row-independence language (design doc §1.16, the `Qc`-non-root form) this is: there is one parent
seed `q₀` and a subfamily `t` of surviving-edge links whose **exterior-projected** panel rows
`(extProj V(H)).dualMap ∘ panelRow ends` are linearly independent at `q₀`, of size `≥ D(|sc|−1)`
(`sc = (V(G)∖V(H)) ∪ {r}`, the surviving body set).

**This rank-attainment across the relabel is the last research-shaped Case-I brick.** No green brick
converts the contraction's relabelled-graph rigidity into the original-endpoint surviving-row
independence: the collapse map `collapseTo r V(H)` redirects each surviving edge's endpoints (hence
which panel normals its support extensor uses), so the green linking-edge brick
(`infinitesimalMotions_eq_of_isLink_span_supportExtensor`, which demands a span-equality of the
support extensors) is *inapplicable* (design doc §1.7 irreducibility — the `hspan` fails), and the
genericity device of Phase 21b does not discharge it either (a distinct obligation, the
collapse-normal mismatch). Recovering the surviving rank at the *un-collapsed* endpoints **is** the
algebraic-independence statement of Claim 6.4. It is therefore carried here as the explicit
hypothesis `htransport`, in the established Phase-21b green-modulo `h…` idiom (exactly as Cases I/II
carried the genericity device before Phase 21b, and as the superseded motion-space form
`rigidContract_rigidity_transport` carried G3a's `∃`-seed version): `lem:claim-6-4` /
`lem:case-I-realization` stay green-modulo, but the obligation is tracked as a single visible
hypothesis pinned to KT eq. (6.9) rather than buried in a `sorry` or an `axiom`, and the brick does
the surrounding plumbing only.

Given `htransport`, the brick is a thin repackaging: it extracts the contraction's generic IH
`⟨Q, hQg, hQgp, hQrig⟩` and forwards the seed `q₀` and the witnessed exterior-projected
surviving-row independence in the exact shape the bounded packaging
`exists_rankPolynomial_of_rigidOn_linking_set_proj` (N-22b-2) consumes for its `hsupp`/`hcount`/
`hindep` hypotheses (over `G.deleteEdges E(H)` at the parent selector `ends`, projecting away the
rigid-block columns `V(H)`). Composing the two (N-22b-3) discharges the composer's `hclaim64`. -/
theorem PanelHingeFramework.rigidContract_exterior_rank_transport [Finite α] [Finite β]
    (G H : Graph α β) (ends : β → α × α) {r : α}
    (n : ℕ) (hne : V(G.rigidContract H r).Nonempty) (hdef : (G.rigidContract H r).deficiency n = 0)
    (hQ : PanelHingeFramework.HasGenericFullRankRealization k n (G.rigidContract H r))
    (htransport : ∀ Q : PanelHingeFramework k α β, Q.graph = G.rigidContract H r →
      Q.IsGeneralPosition →
      Q.toBodyHinge.IsInfinitesimallyRigidOn V(G.rigidContract H r) →
      ∃ q₀ : α × Fin (k + 2) → ℝ,
        ∃ t : Set (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k),
          (∀ i ∈ t, (G.deleteEdges E(H)).IsLink (i : β × _ × _).1
            (ends (i : β × _ × _).1).1 (ends (i : β × _ × _).1).2) ∧
          screwDim k * (((V(G) \ V(H)) ∪ {r}).ncard - 1) ≤ Nat.card t ∧
          LinearIndependent ℝ (fun i : t => (extProj (k := k) V(H)).dualMap
            ((PanelHingeFramework.ofNormals (G.deleteEdges E(H)) ends q₀).toBodyHinge.panelRow
              ends (i : β × _ × _)))) :
    ∃ q₀ : α × Fin (k + 2) → ℝ,
      ∃ t : Set (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k),
        (∀ i ∈ t, (G.deleteEdges E(H)).IsLink (i : β × _ × _).1
          (ends (i : β × _ × _).1).1 (ends (i : β × _ × _).1).2) ∧
        screwDim k * (((V(G) \ V(H)) ∪ {r}).ncard - 1) ≤ Nat.card t ∧
        LinearIndependent ℝ (fun i : t => (extProj (k := k) V(H)).dualMap
          ((PanelHingeFramework.ofNormals (G.deleteEdges E(H)) ends q₀).toBodyHinge.panelRow
            ends (i : β × _ × _))) := by
  obtain ⟨Q, hQg, hQgp, hQrank, _⟩ := hQ
  have hne' : Q.toBodyHinge.graph.vertexSet.Nonempty := by
    rw [PanelHingeFramework.toBodyHinge_graph, hQg]; exact hne
  rw [hdef, sub_zero] at hQrank
  have hVeq : V(G.rigidContract H r) = Q.toBodyHinge.graph.vertexSet := by
    rw [PanelHingeFramework.toBodyHinge_graph, hQg]
  have h1 : 1 ≤ V(G.rigidContract H r).ncard := (Set.ncard_pos (Set.toFinite _)).2 hne
  have hQrig : Q.toBodyHinge.IsInfinitesimallyRigidOn V(G.rigidContract H r) := by
    rw [hVeq, BodyHingeFramework.isInfinitesimallyRigidOn_vertexSet_iff_finrank_span_rigidityRows
        Q.toBodyHinge hne', ← hVeq]
    zify [h1] at hQrank ⊢; exact_mod_cast hQrank
  exact htransport Q hQg hQgp hQrig

/-- **The contraction's vertex set meets the rigid block in exactly the representative body**
(`lem:claim-6-4`, the U4 assembly infra; Katoh–Tanigawa 2011 §6.2, Phase 22b). For a proper rigid
subgraph `H ≤ G` with `r ∈ V(H) ⊆ V(G)`, the contraction's vertex set
`V(G.rigidContract H r) = collapseTo r V(H) '' V(G) = (V(G)∖V(H)) ∪ {r}` meets `V(H)` in exactly
`{r}`: every surviving body of `V(G)∖V(H)` lies outside `V(H)`, and the only collapsed body present
is the representative `r ∈ V(H)`. This is the `hinter` hypothesis the U3b projected-subfamily
extraction `exists_independent_panelRow_subfamily_of_rigidOn_linking_set_proj` needs of the
relabel-leg framework (whose graph is the contraction), proj `= V(H)`. -/
theorem Graph.rigidContract_vertexSet_inter_eq_singleton {α β : Type*}
    (G H : Graph α β) {r : α} (hr : r ∈ V(H)) (hHsub : V(H) ⊆ V(G)) :
    V(G.rigidContract H r) ∩ V(H) = {r} := by
  classical
  rw [Graph.vertexSet_rigidContract]
  apply Set.eq_singleton_iff_unique_mem.2
  refine ⟨⟨⟨r, hHsub hr, by unfold Graph.collapseTo; rw [if_pos hr]⟩, hr⟩, ?_⟩
  rintro x ⟨⟨y, _, rfl⟩, hxH⟩
  unfold Graph.collapseTo at hxH ⊢
  split_ifs with hyH
  · rfl
  · rw [if_neg hyH] at hxH; exact absurd hxH hyH

/-- **KT Claim 6.4 discharged: the contraction's generic IH yields the exterior-projected
surviving-row witness `htransport`** (`lem:claim-6-4`, the U4 assembly; Katoh–Tanigawa 2011 §6.2,
eqs. (6.5)/(6.7)/(6.9), §5.1, Phase 22b route (i) Commit 5). The capstone of the Claim-6.4
discharge: it *produces* the `htransport`-shaped witness `rigidContract_exterior_rank_transport`
formerly took as an explicit hypothesis, by composing the three landed Case-I bricks U3a/U3b/U2 over
the contraction's *strengthened* generic IH `hQcf : HasGenericFullRankRealization k
(G.rigidContract H r)`. With this in hand the composer `case_I_realization` no longer carries any
green-modulo bundle — Claim 6.4 is fully formal.

The assembly (the three Claim-6.4 bricks, KT eq. (6.7)'s degenerate placement `p2` as witness):
* **U3a** (`hasGenericRealization_transport_relabel`): from `hQcf` (= the IH for `Gc.map f`,
  `f := collapseTo r V(H)`, `Gc := G ＼ E(H)`) produce a free-normal framework `F'` on the
  *relabelled* contraction `Gc.map f = G.rigidContract H r` at the relabel selector
  `endsᵐ e := (f (ends e).1, f (ends e).2)`, in general position and rigid on its whole vertex set —
  the rigidity of the IH realization transported to the relabel selector via the strengthened
  motive's link-recording conjunct.
* **U3b** (`exists_independent_panelRow_subfamily_of_rigidOn_linking_set_proj`): from `F'` rigid on
  its vertex set with `V(F'.graph) ∩ V(H) = {r}` (`rigidContract_vertexSet_inter_eq_singleton`),
  extract a subfamily `t` of `Gc.map f`-links whose **exterior-projected collapsed** rows
  `(extProj V(H)).dualMap ∘ F'.panelRow endsᵐ` are independent, of size `≥ D(|V(F'.graph)|−1) =
  D(|sc|−1)` (the surviving rank, KT's bottom-right block — the genuine Claim-6.4 crux, the
  exterior-column projection losing zero rank because `F'` is rigid).
* **U2** (`panelRow_collapseTo_comp_extProj_dualMap`) at **U1** (`degeneratePlacement`): the witness
  seed `q₀ := degeneratePlacement r V(H) nrm'` (KT's `p2`, the collapsed normal field) carries that
  projected-*collapsed* independence per-edge back to the projected-*uncollapsed* rows of
  `ofNormals Gc ends q₀` (both framings read the same support extensor `nrm ∘ f`, the projection
  reconciling the differing endpoints).

The support is translated from `Gc.map f`-links (at `endsᵐ`) to `Gc`-links (at the parent `ends`)
through `Graph.map_isLink` (an edge linking in the relabel is a `Gc`-edge) and the parent selector's
own link-recording `hends`; the count matches because `V(F'.graph) = V(G.rigidContract H r) =
(V(G)∖V(H)) ∪ {r} = sc`. -/
theorem PanelHingeFramework.rigidContract_exterior_rank_transport_htransport
    [Finite α] [Finite β] (G H : Graph α β) (ends : β → α × α) {r : α}
    (hr : r ∈ V(H)) (hHsub : V(H) ⊆ V(G)) (hcSimple : (G.rigidContract H r).Simple)
    {n : ℕ} (hne : V(G.rigidContract H r).Nonempty) (hdef : (G.rigidContract H r).deficiency n = 0)
    (hQcf : PanelHingeFramework.HasGenericFullRankRealization k n (G.rigidContract H r))
    (hends : ∀ e u v, (G.deleteEdges E(H)).IsLink e u v →
      (G.deleteEdges E(H)).IsLink e (ends e).1 (ends e).2) :
    ∀ Q : PanelHingeFramework k α β, Q.graph = G.rigidContract H r →
      Q.IsGeneralPosition →
      Q.toBodyHinge.IsInfinitesimallyRigidOn V(G.rigidContract H r) →
      ∃ q₀ : α × Fin (k + 2) → ℝ,
        ∃ t : Set (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k),
          (∀ i ∈ t, (G.deleteEdges E(H)).IsLink (i : β × _ × _).1
            (ends (i : β × _ × _).1).1 (ends (i : β × _ × _).1).2) ∧
          screwDim k * (((V(G) \ V(H)) ∪ {r}).ncard - 1) ≤ Nat.card t ∧
          LinearIndependent ℝ (fun i : t => (extProj (k := k) V(H)).dualMap
            ((PanelHingeFramework.ofNormals (G.deleteEdges E(H)) ends q₀).toBodyHinge.panelRow
              ends (i : β × _ × _))) := by
  classical
  intro _ _ _ _
  -- Abbreviations: `Gc := G ＼ E(H)`, `f := collapseTo r V(H)`. `Gc.map f = G.rigidContract H r`.
  set Gc := G.deleteEdges E(H) with hGc
  set f := Graph.collapseTo r V(H) with hf
  -- U3a: transport the contraction's generic IH to the relabel selector `endsᵐ := f ∘ ends`.
  obtain ⟨nrm, hgp, hrig⟩ :=
    PanelHingeFramework.hasGenericRealization_transport_relabel Gc f ends hne hdef hQcf hends
  set endsM : β → α × α := fun e => (f (ends e).1, f (ends e).2) with hendsM
  set F' := (PanelHingeFramework.ofNormals (Gc.map f) endsM nrm).toBodyHinge with hF'
  -- `F'.graph = Gc.map f = G.rigidContract H r`; its vertex set is the surviving body set `sc`.
  have hF'g : F'.graph = G.rigidContract H r := by
    rw [hF', PanelHingeFramework.toBodyHinge_graph, PanelHingeFramework.ofNormals_graph]; rfl
  have hr' : r ∈ F'.graph.vertexSet := by
    rw [hF'g, Graph.vertexSet_rigidContract]
    exact ⟨r, hHsub hr, by unfold Graph.collapseTo; rw [if_pos hr]⟩
  have hinter : F'.graph.vertexSet ∩ V(H) = {r} := by
    rw [hF'g]; exact Graph.rigidContract_vertexSet_inter_eq_singleton G H hr hHsub
  have hnev : F'.graph.vertexSet.Nonempty := ⟨r, hr'⟩
  -- The relabel selector records `F'.graph = Gc.map f`'s links (risk (c) brick); the per-hinge
  -- transversality `hne` follows from the general position of the relabel framework's normals.
  have hendsF' : ∀ e u v, F'.graph.IsLink e u v →
      F'.graph.IsLink e (endsM e).1 (endsM e).2 := by
    rw [hF'g, ← (show Gc.map f = G.rigidContract H r from rfl)]
    intro e u v hlink
    -- A `Gc.map f`-link is the `f`-image of a `Gc`-link `Gc.IsLink e x y`; `ends` records *that*
    -- `Gc`-link (`hends`), and `f`-mapping it gives the relabel selector's recorded link.
    rw [Graph.map_isLink] at hlink
    obtain ⟨x, y, hxy, _, _⟩ := hlink
    have := (hends e x y hxy).map f
    rwa [hendsM]
  have hne : ∀ e, F'.graph.IsLink e (endsM e).1 (endsM e).2 → F'.supportExtensor e ≠ 0 := by
    intro e he
    -- The linking edge has distinct endpoints: `F'.graph = G.rigidContract H r` is simple, so
    -- loopless. General position then gives the support extensor nonzero.
    haveI : (G.rigidContract H r).Loopless := hcSimple.toLoopless
    rw [hF'g] at he
    have hne' : (endsM e).1 ≠ (endsM e).2 := he.ne
    refine (PanelHingeFramework.ofNormals (Gc.map f) endsM
      nrm).supportExtensor_ne_zero_of_isGeneralPosition hgp ?_
    rw [PanelHingeFramework.ofNormals_ends]; exact hne'
  -- U3b: extract the projected-collapsed independent surviving subfamily of size `≥ D(|sc|−1)`.
  obtain ⟨t, hsuppM, hcountM, hindepM⟩ :=
    F'.exists_independent_panelRow_subfamily_of_rigidOn_linking_set_proj
      (ends := endsM) (proj := V(H)) (r := r) hendsF' hne hnev hrig hr' hinter
  -- The surviving body set: `V(F'.graph) = V(G.rigidContract H r) = (V(G)∖V(H)) ∪ {r} = sc`.
  have hF'sc : F'.graph.vertexSet = (V(G) \ V(H)) ∪ {r} := by
    rw [hF'g, Graph.vertexSet_rigidContract]
    ext x
    simp only [Set.mem_image, Set.mem_union, Set.mem_diff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨y, hy, rfl⟩
      unfold Graph.collapseTo
      split_ifs with hyH
      · exact Or.inr rfl
      · exact Or.inl ⟨hy, hyH⟩
    · rintro (⟨hx, hxH⟩ | hxr)
      · exact ⟨x, hx, by unfold Graph.collapseTo; rw [if_neg hxH]⟩
      · exact ⟨r, hHsub hr, by unfold Graph.collapseTo; rw [if_pos hr, hxr]⟩
  -- The witness seed `q₀ := degeneratePlacement r V(H) nrm'` (KT's `p2`), `nrm'` the body-curried
  -- U3a placement. U2 carries the projected-collapsed independence back to the
  -- projected-uncollapsed rows of `ofNormals Gc ends q₀`.
  set nrm' : α → Fin (k + 2) → ℝ := fun a i => nrm (a, i) with hnrm'
  -- `nrm = fun p => nrm' p.1 p.2` (product eta): makes the U2 RHS framework *syntactically* `F'`.
  have hnrmeq : nrm = fun p : α × Fin (k + 2) => nrm' p.1 p.2 := by
    funext p; rw [hnrm']
  refine ⟨degeneratePlacement r V(H) nrm', t, ?_, ?_, ?_⟩
  · -- Support: a `Gc.map f`-link is the `f`-image of a `Gc`-link, recorded by the parent `ends`.
    intro i hi
    have := hsuppM i hi
    rw [hF'g, ← (show Gc.map f = G.rigidContract H r from rfl), Graph.map_isLink] at this
    obtain ⟨x, y, hxy, _, _⟩ := this
    exact hends i.1 x y hxy
  · -- Count: `V(F'.graph).ncard = ((V(G)∖V(H)) ∪ {r}).ncard`.
    rwa [hF'sc] at hcountM
  · -- Independence: U2 equates each projected-uncollapsed row with the projected-collapsed
    -- `F'`-row. The U2 RHS framework `ofNormals (Gc.map f) endsM (fun p => nrm' p.1 p.2)` is `F'`:
    -- rewriting `nrm = fun p => nrm' p.1 p.2` (product eta) makes the two frameworks
    -- *syntactically* equal.
    have hrow : (fun i : t => (extProj (k := k) V(H)).dualMap
        ((PanelHingeFramework.ofNormals Gc ends
          (degeneratePlacement r V(H) nrm')).toBodyHinge.panelRow ends (i : β × _ × _)))
        = (fun i : t => (extProj (k := k) V(H)).dualMap (F'.panelRow endsM (i : β × _ × _))) := by
      funext i
      rw [panelRow_collapseTo_comp_extProj_dualMap Gc H hr nrm' ends (i : β × _ × _), hF', hnrmeq]
    rw [hrow]; exact hindepM

/-- **Deficiency-aware `_proj` rank polynomial for the surviving block**
(`lem:rank-polynomial-IH-relabel-proj`,
the V6-b leaf in its route-1 form; Katoh–Tanigawa 2011 §6.2, eqs. (6.5)/(6.9), §5.1, Phase 22i
L5b-ii-b). The deficiency-tolerant sibling of `rigidContract_exterior_rank_transport` followed by
`exists_rankPolynomial_of_rigidOn_linking_set_proj` — the surviving-leg input the simple all-`k`
Case-I producer feeds the block-triangular coupler's `hsc_proj_indep`. From the contraction's IH
(`hKmin` minimal-`k'`-dof, `hQcf` its generic full-rank realization at *possibly-positive*
deficiency `k'`), a `Loopless` hypothesis on the contraction, and the parent surviving-edge
link-recording selector `hends`, it produces a nonzero rational rank polynomial `Q` whose
non-roots `q` carry: a subfamily `rsc` of surviving-edge links whose **exterior-projected**
(`(extProj V(H)).dualMap`) panel rows of `ofNormals (G ＼ E(H)) ends q` are linearly independent of
size `≥ D(|sc|−1) − k'` (`sc = (V(G)∖V(H)) ∪ {r}`, the surviving body set).

This is the route-1 (§1.66) replacement for the route-2 leaf
`exists_rankPolynomial_of_IH_relabel_linking`:
where route 2 produced the *full-span* rank of the contraction framework (the splice brick's input,
which §1.66 found undischargeable for the GP producer — `hFc_surv_le` is a
support-extensor-parallelism
mechanism mismatch), this produces the **exterior-projected surviving-row** rank the coupler
`hasGenericFullRankRealization_of_couple_blockTriangular_ofNormals_set` reads off `F = ofNormals`
itself, exactly as the rigid `case_I_realization` does — only deficiency-aware. Every
`hdef=0`/`hrig`
link of the rigid chain is replaced by a landed deficient analogue:
* **U3a / shared core** (`finrank_span_rigidityRows_ofNormals_relabel_eq`): carries the IH's
  *deficient* rank `D(|V(Gc.map f)|−1) − def` across the collapse-relabel selector swap as a
  finrank equality, supplying the witness placement `nrm` (GP) and its exact rank `N`. The rigid
  `hasGenericRealization_transport_relabel` (which converts to `IsInfinitesimallyRigidOn`) is
  unavailable at `def = k' > 0`.
* **U3b extractor** (`exists_independent_panelRow_subfamily_of_le_finrank_proj`, L5b-ii-a): from the
  rank input `N` and the rigidity-free `hinter : V(F'.graph) ∩ V(H) = {r}` (the L5a-ii
  column-deletion `injOn` core, via `rigidContract_vertexSet_inter_eq_singleton`), extracts a
  projected-collapsed independent surviving subfamily of size `≥ N`. The rigid
  `exists_independent_panelRow_subfamily_of_rigidOn_linking_set_proj` is `hrig`-gated.
* **U2** (`panelRow_collapseTo_comp_extProj_dualMap`, rigidity-free, reused verbatim): carries the
  projected-collapsed independence per-edge from the relabel leg
  `F' = ofNormals (Gc.map f) endsᵐ nrm`
  back to the projected-uncollapsed rows of `ofNormals Gc ends (degeneratePlacement r V(H) nrm')`
  (KT's `p2`), giving a single-placement witness in the shape
  `exists_rankPolynomial_of_rigidOn_linking_set_proj` consumes.
* The bounded packaging (`exists_rankPolynomial_of_rigidOn_linking_set_proj`, unchanged — generic
  in the projected family) lifts that single-placement witness to the `Q`-non-root rank
  polynomial. -/
theorem PanelHingeFramework.exists_rankPolynomial_of_IH_relabel_linking_set_proj
    [DecidableEq β] [Finite α] [Finite β] (G H : Graph α β) (ends : β → α × α) {r : α}
    (hr : r ∈ V(H)) (hHsub : V(H) ⊆ V(G)) {n : ℕ} {k' : ℤ}
    (hKmin : (G.rigidContract H r).IsMinimalKDof n k')
    (hQcf : PanelHingeFramework.HasGenericFullRankRealization k n (G.rigidContract H r))
    (hcLoop : (G.rigidContract H r).Loopless)
    (hends : ∀ e u v, (G.deleteEdges E(H)).IsLink e u v →
      (G.deleteEdges E(H)).IsLink e (ends e).1 (ends e).2) :
    ∃ Q : MvPolynomial (α × Fin (k + 2)) ℝ, Q ≠ 0 ∧
      (Q.coeffs : Set ℝ) ⊆ Set.range (algebraMap ℚ ℝ) ∧
      ∀ q : α × Fin (k + 2) → ℝ, MvPolynomial.eval q Q ≠ 0 →
        ∃ rsc : Set (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k),
          (∀ i ∈ rsc, (G.deleteEdges E(H)).IsLink (i : β × _ × _).1
            (ends (i : β × _ × _).1).1 (ends (i : β × _ × _).1).2) ∧
          screwDim k * (((V(G) \ V(H)) ∪ {r}).ncard - 1) - k' ≤ (Nat.card rsc : ℤ) ∧
          LinearIndependent ℝ (fun i : rsc => (extProj (k := k) V(H)).dualMap
            ((PanelHingeFramework.ofNormals (G.deleteEdges E(H)) ends q).toBodyHinge.panelRow
              ends (i : β × _ × _))) := by
  classical
  -- Abbreviations: `Gc := G ＼ E(H)`, `f := collapseTo r V(H)`; `Gc.map f = G.rigidContract H r`.
  set Gc := G.deleteEdges E(H) with hGc
  set f := Graph.collapseTo r V(H) with hf
  have hGcmap : Gc.map f = G.rigidContract H r := rfl
  -- U3a (shared core): the witness placement `nrm` (GP) with the *deficient* rank equality.
  obtain ⟨nrm, hgp, hrank_eq⟩ :=
    PanelHingeFramework.finrank_span_rigidityRows_ofNormals_relabel_eq Gc f ends hQcf hends
  set endsM : β → α × α := fun e => (f (ends e).1, f (ends e).2) with hendsM
  set F' := (PanelHingeFramework.ofNormals (Gc.map f) endsM nrm).toBodyHinge with hF'
  -- `F'.graph = Gc.map f = G.rigidContract H r`; vertex set = the surviving body set `sc`.
  have hF'g : F'.graph = G.rigidContract H r := by
    rw [hF', PanelHingeFramework.toBodyHinge_graph, PanelHingeFramework.ofNormals_graph]; rfl
  have hinter : F'.graph.vertexSet ∩ V(H) = {r} := by
    rw [hF'g]; exact Graph.rigidContract_vertexSet_inter_eq_singleton G H hr hHsub
  -- The relabel selector records `F'.graph = Gc.map f`'s links; per-hinge transversality from GP.
  have hendsF' : ∀ e u v, F'.graph.IsLink e u v →
      F'.graph.IsLink e (endsM e).1 (endsM e).2 := by
    rw [hF'g, ← hGcmap]
    intro e u v hlink
    rw [Graph.map_isLink] at hlink
    obtain ⟨x, y, hxy, _, _⟩ := hlink
    have := (hends e x y hxy).map f
    rwa [hendsM]
  have hneF' : ∀ e, F'.graph.IsLink e (endsM e).1 (endsM e).2 → F'.supportExtensor e ≠ 0 := by
    intro e he
    haveI : (G.rigidContract H r).Loopless := hcLoop
    rw [hF'g] at he
    have hne' : (endsM e).1 ≠ (endsM e).2 := he.ne
    refine (PanelHingeFramework.ofNormals (Gc.map f) endsM
      nrm).supportExtensor_ne_zero_of_isGeneralPosition hgp ?_
    rw [PanelHingeFramework.ofNormals_ends]; exact hne'
  -- The witness rank `N := finrank (span F'.rigidityRows)`; the shared core's ℤ-equality reads
  -- `(N : ℤ) = D(|V(Gc.map f)|−1) − def`, which `hF'sc` + `hKmin.1` rewrite to `D(|sc|−1)−k'`.
  set N := Module.finrank ℝ (Submodule.span ℝ F'.rigidityRows) with hN_def
  have hF'sc : F'.graph.vertexSet = (V(G) \ V(H)) ∪ {r} := by
    rw [hF'g, Graph.vertexSet_rigidContract]
    ext x
    simp only [Set.mem_image, Set.mem_union, Set.mem_diff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨y, hy, rfl⟩
      unfold Graph.collapseTo
      split_ifs with hyH
      · exact Or.inr rfl
      · exact Or.inl ⟨hy, hyH⟩
    · rintro (⟨hx, hxH⟩ | hxr)
      · exact ⟨x, hx, by unfold Graph.collapseTo; rw [if_neg hxH]⟩
      · exact ⟨r, hHsub hr, by unfold Graph.collapseTo; rw [if_pos hr, hxr]⟩
  have hNval : (N : ℤ) = screwDim k * (((V(G) \ V(H)) ∪ {r}).ncard - 1) - k' := by
    -- After the `endsM`/`N` `set`s, the shared core's `hrank_eq` reads
    -- `(N : ℤ) = D(|V(Gc.map f)|−1) − def`; `V(Gc.map f) = V(F'.graph) = sc` (`hF'sc`) and
    -- `def(Gc.map f) = k'` from `hKmin.1`. (Do NOT `rw [hN_def]` first — `set N` already folded
    -- `hrank_eq`'s LHS to `N`; rewriting `N` back to `finrank` unmatches it; TACTICS-QUIRKS §43.)
    have hdefeq : (Gc.map f).deficiency n = k' := by rw [hGcmap]; exact hKmin.1
    have hncard : (V(Gc.map f).ncard : ℤ) = ((V(G) \ V(H)) ∪ {r}).ncard := by
      rw [show V(Gc.map f) = F'.graph.vertexSet from by rw [hF'g, hGcmap], hF'sc]
    -- `sc = (V(G)∖V(H)) ∪ {r}` is nonempty (contains `r`), so the ℕ-subtraction `(ncard−1)` of
    -- `hrank_eq`'s RHS coerces to the ℤ-subtraction `↑ncard − 1` of the target (`Nat.cast_sub`).
    have h1 : 1 ≤ ((V(G) \ V(H)) ∪ {r}).ncard :=
      Set.ncard_pos (Set.toFinite _) |>.2 ⟨r, Set.mem_union_right _ rfl⟩
    rw [hrank_eq, hdefeq, hncard, Nat.cast_sub h1, Nat.cast_one]
  -- U3b (L5b-ii-a extractor): the projected-collapsed independent surviving subfamily, size `≥ N`.
  obtain ⟨t, hsuppM, hcountM, hindepM⟩ :=
    F'.exists_independent_panelRow_subfamily_of_le_finrank_proj
      (ends := endsM) (proj := V(H)) (r := r) hendsF' hneF' hinter (le_refl N)
  -- U2 + U1 (degenerate placement): carry the projected-collapsed independence back to the
  -- projected-uncollapsed rows of `ofNormals Gc ends (degeneratePlacement r V(H) nrm')` (KT `p2`).
  set nrm' : α → Fin (k + 2) → ℝ := fun a i => nrm (a, i) with hnrm'
  have hnrmeq : nrm = fun p : α × Fin (k + 2) => nrm' p.1 p.2 := by funext p; rw [hnrm']
  -- The single-placement witness `(q₀ := degeneratePlacement …, t)` in the packaging's shape.
  have hsupp₀ : ∀ i ∈ t, Gc.IsLink (i : β × _ × _).1 (ends (i : β × _ × _).1).1
      (ends (i : β × _ × _).1).2 := by
    intro i hi
    have := hsuppM i hi
    rw [hF'g, ← hGcmap, Graph.map_isLink] at this
    obtain ⟨x, y, hxy, _, _⟩ := this
    exact hends i.1 x y hxy
  have hindep₀ : LinearIndependent ℝ (fun i : t => (extProj (k := k) V(H)).dualMap
      ((PanelHingeFramework.ofNormals Gc ends
        (degeneratePlacement r V(H) nrm')).toBodyHinge.panelRow ends (i : β × _ × _))) := by
    have hrow : (fun i : t => (extProj (k := k) V(H)).dualMap
        ((PanelHingeFramework.ofNormals Gc ends
          (degeneratePlacement r V(H) nrm')).toBodyHinge.panelRow ends (i : β × _ × _)))
        = (fun i : t => (extProj (k := k) V(H)).dualMap (F'.panelRow endsM (i : β × _ × _))) := by
      funext i
      rw [panelRow_collapseTo_comp_extProj_dualMap Gc H hr nrm' ends (i : β × _ × _), hF', hnrmeq]
    rw [hrow]; exact hindepM
  -- The bounded packaging lifts the single-placement witness to the `Q`-non-root rank polynomial.
  obtain ⟨Q, hQne, hQrat, hQ⟩ :=
    PanelHingeFramework.exists_rankPolynomial_of_rigidOn_linking_set_proj (k := k)
      Gc ends V(H) (m := N) hsupp₀ hcountM hindep₀
  refine ⟨Q, hQne, hQrat, fun q hq => ?_⟩
  obtain ⟨rsc, hrsc_supp, hrsc_card, hrsc_indep⟩ := hQ q hq
  refine ⟨rsc, hrsc_supp, ?_, hrsc_indep⟩
  -- The count: `N ≤ |rsc|` (ℕ) and `(N : ℤ) = D(|sc|−1) − k'` give the ℤ target.
  rw [← hNval]; exact_mod_cast hrsc_card

/-- **An independent family whose span lies in the rigidity rows, of size `≥ D(|V(G)|−1)`, forces
rigidity on `V(G)`** (`lem:case-I-realization` / `lem:case-III`, the device-row-addition closure,
span-containment core; Katoh–Tanigawa 2011 §6.2 eq. (6.3), Phases 22a/22g). The block-triangular
reframing's device-side closure (design doc §1.14): rather than gluing two legs at a *common seed*
(the motion-space splice `isInfinitesimallyRigidOn_of_splice`, which demands one placement rigid on
both legs), exhibit enough **independent rows spanning into the rigidity rows** of the single common
framework `F` and read rigidity off the row count. From any linearly independent family
`a : ι → Module.Dual ℝ (α → ScrewSpace k)` with `span (range a) ≤ span F.rigidityRows` (`hsub`) and
`Nat.card ι ≥ D(|V(G)|−1)` (`hcard`), the rank-nullity identity
`dim Z(F) = D|V| − finrank (span rigidityRows) ≤ D|V| − D(|V|−1) = D` upgrades, via the
relative-count adapter N3 (`isInfinitesimallyRigidOn_vertexSet_of_finrank_le`), to infinitesimal
rigidity on `V(G)`.

The span-containment hypothesis `hsub` (rather than pointwise membership `a i ∈ rigidityRows`) is
what the `d = 3` candidate-completion path needs: its `+1` candidate row `hingeRow v b r̂` is a
*combination* `∑ λ_j hingeRow v b r_j` of `e_b`-panel rows, a member of `span rigidityRows` but not
of the bare set `rigidityRows` (KT §6.4.1 eqs. (6.27)/(6.29); design doc §1.35). The pointwise
wrapper `isInfinitesimallyRigidOn_vertexSet_of_independent_rigidityRows` recovers the `hmem` form
for the block-triangular Case-I `Sum.elim` of `H`-block and surviving-edge rows.

This is the same rank-nullity argument the rank-polynomial consumer
`isInfinitesimallyRigidOn_ofNormals_of_rankPolynomial_ne_zero_linking` runs, but over an *arbitrary*
finite index family rather than a `Set`-subfamily. Crucially it concludes rigidity of `F` *itself*
(at its own seed), so when `F = ofNormals G ends q₀` with `q₀` general position the conclusion lifts
to the *generic* motive — no device round-trip, general position survives. -/
theorem BodyHingeFramework.isInfinitesimallyRigidOn_vertexSet_of_span_le_rigidityRows
    [Finite α] (F : BodyHingeFramework k α β) {ι : Type*} [Finite ι]
    {a : ι → Module.Dual ℝ (α → ScrewSpace k)} (hLI : LinearIndependent ℝ a)
    (hsub : Submodule.span ℝ (Set.range a) ≤ Submodule.span ℝ F.rigidityRows)
    (hne : F.graph.vertexSet.Nonempty)
    (hcard : screwDim k * (F.graph.vertexSet.ncard - 1) ≤ Nat.card ι) :
    F.IsInfinitesimallyRigidOn F.graph.vertexSet := by
  classical
  haveI : Fintype α := Fintype.ofFinite α
  haveI : Fintype ι := Fintype.ofFinite ι
  -- The independent family spans a subspace of the rigidity-row span of dimension `Nat.card ι`.
  have hrows : Nat.card ι ≤ Module.finrank ℝ (Submodule.span ℝ F.rigidityRows) := by
    rw [Nat.card_eq_fintype_card, ← finrank_span_eq_card hLI]
    exact Submodule.finrank_mono hsub
  -- Rank-nullity: `dim Z = D|V| − finrank (span rigidityRows) ≤ D|V| − D(|V|−1) = D`.
  have hcompl : Module.finrank ℝ F.infinitesimalMotions
      + Module.finrank ℝ (Submodule.span ℝ F.rigidityRows)
      = screwDim k * Fintype.card α := by
    rw [F.infinitesimalMotions_eq_dualCoannihilator, Subspace.finrank_dualCoannihilator_eq,
      add_comm, Subspace.finrank_add_finrank_dualAnnihilator_eq, Subspace.dual_finrank_eq,
      BodyHingeFramework.finrank_screwAssignment]
  have hsplit : screwDim k * Fintype.card α
      = screwDim k * F.graph.vertexSet.ncard + screwDim k * (F.graph.vertexSet)ᶜ.ncard := by
    rw [← Nat.mul_add, Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card]
  have h1 : 1 ≤ F.graph.vertexSet.ncard := (Set.ncard_pos (Set.toFinite _)).2 hne
  rw [Nat.mul_sub, Nat.mul_one] at hcard
  refine F.isInfinitesimallyRigidOn_vertexSet_of_finrank_le hne ?_
  rw [Nat.mul_succ]
  omega

/-- **An independent family of rigidity rows of size `≥ D(|V(G)|−1)` forces rigidity on `V(G)`**
(`lem:case-I-realization`, the device-row-addition closure, pointwise-membership form;
Katoh–Tanigawa 2011 §6.2 eq. (6.3), Phase 22a). The pointwise wrapper of
`isInfinitesimallyRigidOn_vertexSet_of_span_le_rigidityRows`: when every row of the independent
family is *literally* a rigidity row (`hmem : ∀ i, a i ∈ F.rigidityRows`), the span containment is
`Submodule.span_le.2`. Block-triangular Case-I assembly (`Sum.elim` of the `H`-block and
surviving-edge rows) feeds this; the candidate-completion path (whose `+1` row is a *combination* of
panel rows, not a single rigidity row) feeds the span-containment core instead. -/
theorem BodyHingeFramework.isInfinitesimallyRigidOn_vertexSet_of_independent_rigidityRows
    [Finite α] (F : BodyHingeFramework k α β) {ι : Type*} [Finite ι]
    {a : ι → Module.Dual ℝ (α → ScrewSpace k)} (hLI : LinearIndependent ℝ a)
    (hmem : ∀ i, a i ∈ F.rigidityRows) (hne : F.graph.vertexSet.Nonempty)
    (hcard : screwDim k * (F.graph.vertexSet.ncard - 1) ≤ Nat.card ι) :
    F.IsInfinitesimallyRigidOn F.graph.vertexSet :=
  F.isInfinitesimallyRigidOn_vertexSet_of_span_le_rigidityRows hLI
    (Submodule.span_le.2 (fun _ ⟨i, hi⟩ => hi ▸ Submodule.subset_span (hmem i))) hne hcard

/-- **Case I shared-seed coupling, *block-triangular* body-set form** (`lem:case-I-realization`, the
block-triangular reframing N6-G3-G3c-iii-b; Katoh–Tanigawa 2011 §6.2, eqs. (6.3), (6.5), (6.6),
(6.9), Phase 22a). The honest replacement for the asymmetric coupling
`hasGenericFullRankRealization_of_couple_asymm_ofNormals_set` (design doc §1.14). The asymmetric
coupling routed the contraction leg's rigidity-on-`sc`-at-`q₀` through the motion-space splice glue
`isInfinitesimallyRigidOn_of_splice`, which demands one placement rigid on *both* legs; supplying
that rigidity required the undischargeable `htransportGP` ("GP ⟹ rigid", false — design doc §1.13).

This coupling reproduces KT eq. (6.3)'s **block-triangular rank-addition** over the *single* common
framework `F = ofNormals G ends q₀` instead. It exhibits `D(|V(G)|−1)` independent rigidity rows of
`F`, split block-wise (`Sum.elim`, Piece B):
* **`s_H`** — `≥ D(|sH|−1)` rows of the rigid-block edges `E(GH)`, independent at `q₀` from the
  `H`-leg's rank polynomial (`exists_rankPolynomial_of_rigidOn_linking_set`). The block-triangular
  path uses only the `H`-block *rows* (not rigidity of the parent at a shared seed), so the `H`-leg
  needs *no* complement-isolation equality here — only its own rigidity on `sH` (the legitimate,
  honest round-trip, the `H`-leg being rigid on its *full* vertex set `sH`). Each row's endpoints
  lie in `V(GH) ⊆ sH` (`hsHV`);
* **`s_c`** — `≥ D(|sc|−1)` surviving-edge rows of `E(Gc)`, supplied by the Claim-6.4 hypothesis
  `hsc_proj_indep` **after the exterior-column projection** `D := (extProj sH).dualMap` onto the
  columns `α ∖ sH`, conditioned on the contraction **rank-polynomial `Qc`-non-root** (KT eq. (6.9)'s
  generic placement, a Zariski-open locus).

The block-triangular core (Piece B): the `H`-rows vanish under `D` (`hingeRow_comp_extProj_eq_zero`,
both endpoints in `sH` — KT's top-right `0`), so `span s_H ⊆ ker D`; the projected `s_c`-rows are
independent (`hsc_proj_indep`), so `s_c` is independent (`LinearIndependent.of_comp`) and disjoint
from `ker D` (`Submodule.range_ker_disjoint`), whence `Disjoint (span s_H) (span s_c)` and the union
`Sum.elim` is independent (`LinearIndependent.sum_type`). With both blocks' rows lying in `F`'s
rigidity rows and summing to `≥ D(|V(G)|−1)` (cover + shared body `c`), the device-row closure
`isInfinitesimallyRigidOn_vertexSet_of_independent_rigidityRows` makes `F = ofNormals G ends q₀`
rigid on `V(G)` *at `q₀` itself*; since `q₀` is general position the *generic* motive holds.

**This eliminates the common-seed demand by construction** (the device-row closure reads independent
*rows*, never rigidity of `F` on a leg at a shared seed). The single green-modulo hypothesis is
`hsc_proj_indep` (KT's bottom-right block rank `rank R(G,p;E∖E′,V∖V′) = D(|sc|−1)`, eq. (6.5)/(6.9)
+ Lemma 5.1), stated as exterior-*projected* row-independence **conditioned on a rank-polynomial
`Qc`-non-root**: the contraction obligation is delivered *at the construction's own seed* `q₀` (the
triple-product `Q_H · Q_c · Q_gp` non-root), which is the Zariski-open generic locus KT eq. (6.9)
asserts — **not** every general-position placement (the over-quantified `∀`-GP shape, which is
strictly stronger and undischargeable). It is contraction-leg-local (only the surviving edges, only
their exterior-projected rows) and a row-count — the genuine, dischargeable Claim 6.4. -/
theorem PanelHingeFramework.hasGenericFullRankRealization_of_couple_blockTriangular_ofNormals_set
    [Finite α] [Finite β] (G : Graph α β) (ends : β → α × α)
    (hends : ∀ e u v, G.IsLink e u v → G.IsLink e (ends e).1 (ends e).2)
    {GH Gc : Graph α β} (hGH : GH ≤ G) (hGc : Gc ≤ G)
    {sH sc : Set α} {c : α} (hcH : c ∈ sH) (hcc : c ∈ sc) (hcover : V(G) ⊆ sH ∪ sc)
    (hneG : V(G).Nonempty) (hnesH : sH.Nonempty) (hsHV : V(GH) ⊆ sH)
    {qH : α × Fin (k + 2) → ℝ}
    (hneH : ∀ e, GH.IsLink e (ends e).1 (ends e).2 →
      (PanelHingeFramework.ofNormals GH ends qH).toBodyHinge.supportExtensor e ≠ 0)
    (hrigH :
      (PanelHingeFramework.ofNormals GH ends qH).toBodyHinge.IsInfinitesimallyRigidOn sH)
    -- The contraction block's surviving-edge rows are independent **after the exterior-column
    -- projection** onto `α ∖ sH` (`extProj sH`), of size `≥ D(|sc|−1)` (KT's bottom-right block
    -- rank, eq. (6.5)/(6.9)). Conditioned on a **rank-polynomial `Qc`-non-root** (KT eq. (6.9)'s
    -- generic placement, a Zariski-open locus), threaded into the shared seed via the triple
    -- product `Q_H · Q_c · Q_gp`. Each row's edge links in `Gc`.
    (Qc : MvPolynomial (α × Fin (k + 2)) ℝ) (hQc_ne : Qc ≠ 0)
    (hQc_rat : (Qc.coeffs : Set ℝ) ⊆ Set.range (algebraMap ℚ ℝ))
    (hsc_proj_indep : ∀ q : α × Fin (k + 2) → ℝ, MvPolynomial.eval q Qc ≠ 0 →
      ∃ rsc : Set (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k),
        (∀ i ∈ rsc, Gc.IsLink (i : β × _ × _).1 (ends (i : β × _ × _).1).1
          (ends (i : β × _ × _).1).2) ∧
        screwDim k * (sc.ncard - 1) ≤ Nat.card rsc ∧
        LinearIndependent ℝ (fun i : rsc => (extProj (k := k) sH).dualMap
          ((PanelHingeFramework.ofNormals G ends q).toBodyHinge.panelRow ends (i : β × _ × _))))
    (n : ℕ) (hdef : G.deficiency n = 0) :
    PanelHingeFramework.HasGenericFullRankRealization k n G := by
  classical
  haveI : Fintype α := Fintype.ofFinite α
  -- The parent's edge-restricted `hends` weakens to the `H`-leg (the only leg running the
  -- rank-polynomial round-trip).
  have hendsH : ∀ e u v, GH.IsLink e u v → GH.IsLink e (ends e).1 (ends e).2 := fun e u v h =>
    (Graph.IsSubgraph.isLink_iff hGH h.edge_mem).mpr
      (hends e u v ((Graph.IsSubgraph.isLink_iff hGH h.edge_mem).mp h))
  -- (i) The `H`-leg's body-set leg-restricted rank polynomial at its own seed `qH` (rational). Each
  -- witnessed index links in `GH` (`hsuppH`), so both its endpoints lie in `V(GH) ⊆ sH`.
  obtain ⟨rsH, QH, hsuppH, hcardH, hQ0H, hQHrat, hLIH⟩ :=
    PanelHingeFramework.exists_rankPolynomial_of_rigidOn_linking_set GH ends hendsH hneH hnesH hrigH
  -- (ii) The general-position factor (rational).
  obtain ⟨Qgp, hQgp_ne, hQgprat, hQgp_pos⟩ :=
    exists_generalPosition_polynomial (k := k) G ends
  -- (iii) All three of `Q_H`, `Q_c` (`hQc_rat`), `Q_gp` are rational, so an algebraically-
  -- independent-over-`ℚ` seed `q₀` is a simultaneous non-root (H-block LI + the contraction rank
  -- polynomial `Q_c`'s generic locus + general position), and carries the alg-independence
  -- conjunct.
  have hQHne : QH ≠ 0 := fun h => hQ0H (by rw [h, map_zero])
  have hQgpne : Qgp ≠ 0 := by
    obtain ⟨f, hf⟩ := Countable.exists_injective_nat α
    refine fun h => hQgp_ne (fun a => (f a : ℝ)) ?_ (by rw [h, map_zero])
    exact fun a b hab => hf (Nat.cast_injective hab)
  obtain ⟨q₀, _, halg⟩ := exists_injective_algebraicIndependent_real (α × Fin (k + 2))
  have hq₀H : MvPolynomial.eval q₀ QH ≠ 0 :=
    MvPolynomial.eval_ne_zero_of_coeffs_subset_range_of_algebraicIndependent halg hQHrat hQHne
  have hq₀c : MvPolynomial.eval q₀ Qc ≠ 0 :=
    MvPolynomial.eval_ne_zero_of_coeffs_subset_range_of_algebraicIndependent halg hQc_rat hQc_ne
  have hq₀gp : MvPolynomial.eval q₀ Qgp ≠ 0 :=
    MvPolynomial.eval_ne_zero_of_coeffs_subset_range_of_algebraicIndependent halg hQgprat hQgpne
  have hgp : (PanelHingeFramework.ofNormals (k := k) G ends q₀).IsGeneralPosition :=
    hQgp_pos q₀ hq₀gp
  -- Abbreviations: the parent framework at `q₀`, the exterior-column projection's dual map `D`.
  set F := (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge with hF
  set D := (extProj (k := k) sH).dualMap with hD
  -- (iv-H) The `H`-block rows of `F` indexed by `rsH`, independent at `q₀`.
  have hLIH₀ : LinearIndependent ℝ (fun i : rsH => F.panelRow ends (i : β × _ × _)) := hLIH q₀ hq₀H
  -- (iv-c) The surviving-edge block: exterior-projected independent at the `Q_c`-non-root seed.
  obtain ⟨rsc, hsuppc, hcardc, hprojc⟩ := hsc_proj_indep q₀ hq₀c
  -- A panel row of `F` whose edge links in `G` is one of `F`'s rigidity rows.
  have hrow_mem : ∀ (i : β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k),
      G.IsLink i.1 (ends i.1).1 (ends i.1).2 → F.panelRow ends i ∈ F.rigidityRows := by
    rintro ⟨e', t₁, t₂⟩ hlink
    exact ⟨e', (ends e').1, (ends e').2, hlink,
      annihRow (F.supportExtensor e') t₁ t₂, by
        rw [BodyHingeFramework.hingeRowBlock_apply, Submodule.mem_dualAnnihilator]
        intro x hx
        rw [Submodule.mem_span_singleton] at hx
        obtain ⟨ρ, rfl⟩ := hx
        rw [map_smul, annihRow_apply_self, smul_zero], rfl⟩
  -- Each `H`-block row vanishes under `D = (extProj sH).dualMap` (both endpoints in `V(GH) ⊆ sH`,
  -- so `hingeRow_comp_extProj_eq_zero`): the row-side of KT's top-right `0`.
  have hH_ker : ∀ i : rsH, D (F.panelRow ends (i : β × _ × _)) = 0 := by
    rintro ⟨⟨e', t₁, t₂⟩, hi⟩
    have hlink := hsuppH _ hi
    rw [hD, BodyHingeFramework.panelRow, LinearMap.dualMap_apply',
      hingeRow_comp_extProj_eq_zero (hsHV hlink.left_mem) (hsHV hlink.right_mem)]
  -- (Piece B) Union-independence of the `H`-block and surviving-edge rows.
  have hcindep : LinearIndependent ℝ (fun i : rsc => F.panelRow ends (i : β × _ × _)) :=
    LinearIndependent.of_comp D hprojc
  have hcdisj : Disjoint (Submodule.span ℝ (Set.range
      (fun i : rsc => F.panelRow ends (i : β × _ × _)))) (LinearMap.ker D) :=
    Submodule.range_ker_disjoint hprojc
  have hHspan : Submodule.span ℝ (Set.range (fun i : rsH => F.panelRow ends (i : β × _ × _)))
      ≤ LinearMap.ker D :=
    Submodule.span_le.2 (fun _ ⟨i, hi⟩ => hi ▸ LinearMap.mem_ker.2 (hH_ker i))
  have hdisj : Disjoint (Submodule.span ℝ (Set.range
      (fun i : rsH => F.panelRow ends (i : β × _ × _))))
      (Submodule.span ℝ (Set.range (fun i : rsc => F.panelRow ends (i : β × _ × _)))) :=
    Disjoint.mono_left hHspan hcdisj.symm
  have hunion : LinearIndependent ℝ
      (Sum.elim (fun i : rsH => F.panelRow ends (i : β × _ × _))
        (fun i : rsc => F.panelRow ends (i : β × _ × _))) :=
    hLIH₀.sum_type hcindep hdisj
  -- Every row of the union is a rigidity row of `F` (its edge links in `G`, by the two subgraphs).
  have hmem : ∀ i : rsH ⊕ rsc, Sum.elim (fun i : rsH => F.panelRow ends (i : β × _ × _))
      (fun i : rsc => F.panelRow ends (i : β × _ × _)) i ∈ F.rigidityRows := by
    rintro (⟨i, hi⟩ | ⟨i, hi⟩)
    · exact hrow_mem _ ((Graph.IsSubgraph.isLink_iff hGH (hsuppH _ hi).edge_mem).mp (hsuppH _ hi))
    · exact hrow_mem _ ((Graph.IsSubgraph.isLink_iff hGc (hsuppc _ hi).edge_mem).mp (hsuppc _ hi))
  -- The two blocks sum to `≥ D(|V(G)|−1)` rows (cover + shared body `c`).
  have hcard : screwDim k * (V(G).ncard - 1) ≤ Nat.card (rsH ⊕ rsc) := by
    rw [Nat.card_sum]
    -- `|sH ∪ sc| + |sH ∩ sc| = |sH| + |sc|`, `1 ≤ |sH ∩ sc|` (shared `c`), `|V(G)| ≤ |sH ∪ sc|`.
    have hunion_card := Set.ncard_union_add_ncard_inter sH sc
    have hinter : 1 ≤ (sH ∩ sc).ncard :=
      (Set.ncard_pos (Set.toFinite _)).2 ⟨c, hcH, hcc⟩
    have hcov : V(G).ncard ≤ (sH ∪ sc).ncard := Set.ncard_le_ncard hcover (Set.toFinite _)
    have h1H : 1 ≤ sH.ncard := (Set.ncard_pos (Set.toFinite _)).2 hnesH
    -- `D(|sH|−1) + D(|sc|−1) ≥ D(|V(G)|−1)`.
    have hkey : screwDim k * (V(G).ncard - 1)
        ≤ screwDim k * (sH.ncard - 1) + screwDim k * (sc.ncard - 1) := by
      rw [← Nat.mul_add]
      apply Nat.mul_le_mul_left
      omega
    omega
  -- (v) The device-row closure makes `F = ofNormals G ends q₀` rigid on `V(G)` at `q₀` itself; with
  -- `q₀` general position the strengthened generic motive holds. The witness is `F`; the
  -- link-recording conjunct is the seed selector's link-recording (`hends`), and the
  -- algebraic-independence conjunct is `halg` (the seed's normals *are* `q₀`).
  refine ⟨PanelHingeFramework.ofNormals G ends q₀,
    PanelHingeFramework.ofNormals_graph G ends q₀, hgp, ?_,
    PanelHingeFramework.ofNormals_recordsLinks_of_hends G ends q₀ hends, halg⟩
  have hFG : F.graph.vertexSet = V(G) := by
    rw [hF, PanelHingeFramework.toBodyHinge_graph, PanelHingeFramework.ofNormals_graph]
  have hrig := F.isInfinitesimallyRigidOn_vertexSet_of_independent_rigidityRows hunion hmem
    (by rw [hFG]; exact hneG) (by rw [hFG]; exact hcard)
  rw [hFG] at hrig
  -- Convert rigidity to rank via W2 + hdef.
  have hne' : F.graph.vertexSet.Nonempty := by rw [hFG]; exact hneG
  have hW2 := F.finrank_span_rigidityRows_of_rigidOn hne' (by rw [hFG]; exact hrig)
  have hVncard : F.graph.vertexSet.ncard = V(G).ncard := by rw [hFG]
  have h1 : 1 ≤ V(G).ncard := (Set.ncard_pos (Set.toFinite _)).2 hneG
  rw [hVncard] at hW2
  rw [← hF, hdef, sub_zero]
  zify [h1] at hW2 ⊢
  exact_mod_cast hW2

/-- **The single-graph bare→generic upgrade** (`lem:case-III-claim612-line-in-panel-union` /
`lem:case-III-realization`, the GAP-2 keystone of the `d = 3` `hsplit` producer; Katoh–Tanigawa 2011
§6.2, Lemma 5.2 "convert to a nonparallel realization without decreasing rank" (printed p. 678,
footnote 4 p. 662); Phase 22g, design doc §1.45). The `d = 3` Case-III producer builds the
eq.-(6.12) degenerate candidate by shearing body `v`'s normal to `n_a + t·n'`, so the candidate seed
is `ℚ`-algebraically *dependent* by construction and cannot itself carry the
`AlgebraicIndependent ℚ` conjunct of the *generic* motive `HasGenericFullRankRealization k G`. But
that motive's realizing framework is **existentially quantified** — it asks for *some*
general-position alg-independent rigid framework on `G`, not for the candidate seed to be generic.
So the producer hands the degenerate candidate to a bare full-rank realization
(`case_III_realization_of_line` → C1), then this single-graph upgrade re-realizes it generically.

The upgrade is `exists_rankPolynomial_of_rigidOn_linking` read for one graph: from the rigid
`ofNormals G ends q₀` (with linking hinges transversal, `hne`) it builds the rational rank
polynomial `Q` — a function of `G` and `ends` *only*, with the seed entering solely through
`eval q₀ Q ≠ 0` (so the candidate's witness line `L` is discarded once full rank is witnessed). The
general-position factor `Qgp` (`exists_generalPosition_polynomial`) is rational too, so an
algebraically-independent-over-`ℚ` seed `q₁` (`exists_injective_algebraicIndependent_real`) is a
simultaneous non-root of both — giving `D(|V(G)|−1)` independent rigidity rows of `ofNormals G ends
q₁` (hence rigid on `V(G)`), general position, the link-recording selector, and the
alg-independence conjunct at once. This is KT's own argument (a degenerate witness gives the rank
lower bound; genericity, which maximizes rank over nonparallel realizations, then supplies the
nonparallel realization at `≥` that rank). It reuses the `case_I_realization` rank-polynomial block
over a *single* graph rather than the two-block splice. -/
theorem PanelHingeFramework.hasGenericFullRankRealization_of_rigidOn_ofNormals
    [Finite α] [Finite β] (G : Graph α β) (ends : β → α × α)
    (hends : ∀ e u v, G.IsLink e u v → G.IsLink e (ends e).1 (ends e).2)
    {q₀ : α × Fin (k + 2) → ℝ}
    (hne : ∀ e, G.IsLink e (ends e).1 (ends e).2 →
      (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.supportExtensor e ≠ 0)
    (hnev : V(G).Nonempty)
    (hrig : (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.IsInfinitesimallyRigidOn V(G))
    (n : ℕ) (hdef : G.deficiency n = 0) :
    PanelHingeFramework.HasGenericFullRankRealization k n G := by
  classical
  -- (i) The single graph's leg-restricted rank polynomial at the degenerate seed `q₀` (rational);
  -- its witnessed index family `s` links in `G` (`hsupp`), has full size, and is independent at
  -- every non-root of `Q`.
  obtain ⟨s, Q, hsupp, hscard, hQ0, hQrat, hLI⟩ :=
    PanelHingeFramework.exists_rankPolynomial_of_rigidOn_linking G ends hends hne hnev hrig
  -- (ii) The general-position factor (rational).
  obtain ⟨Qgp, hQgp_ne, hQgprat, hQgp_pos⟩ := exists_generalPosition_polynomial (k := k) G ends
  have hQne : Q ≠ 0 := fun h => hQ0 (by rw [h, map_zero])
  have hQgpne : Qgp ≠ 0 := by
    obtain ⟨f, hf⟩ := Countable.exists_injective_nat α
    refine fun h => hQgp_ne (fun a => (f a : ℝ)) ?_ (by rw [h, map_zero])
    exact fun a b hab => hf (Nat.cast_injective hab)
  -- (iii) An algebraically-independent-over-`ℚ` seed `q₁` is a simultaneous non-root of `Q` (rank)
  -- and `Qgp` (general position), and carries the alg-independence conjunct.
  obtain ⟨q₁, _, halg⟩ := exists_injective_algebraicIndependent_real (α × Fin (k + 2))
  have hq₁Q : MvPolynomial.eval q₁ Q ≠ 0 :=
    MvPolynomial.eval_ne_zero_of_coeffs_subset_range_of_algebraicIndependent halg hQrat hQne
  have hq₁gp : MvPolynomial.eval q₁ Qgp ≠ 0 :=
    MvPolynomial.eval_ne_zero_of_coeffs_subset_range_of_algebraicIndependent halg hQgprat hQgpne
  have hgp : (PanelHingeFramework.ofNormals (k := k) G ends q₁).IsGeneralPosition :=
    hQgp_pos q₁ hq₁gp
  set F := (PanelHingeFramework.ofNormals G ends q₁).toBodyHinge with hF
  -- (iv) The `s`-subfamily of `F`'s panel rows is independent at `q₁` and lies in `F.rigidityRows`
  -- (every member links in `G`), summing to `≥ D(|V(G)|−1)` rows — the device-row closure then
  -- makes `F = ofNormals G ends q₁` rigid on `V(G)` at `q₁` itself; with `q₁` general position the
  -- strengthened generic motive holds.
  have hLI₁ : LinearIndependent ℝ (fun i : s => F.panelRow ends (i : β × _ × _)) := hLI q₁ hq₁Q
  -- A panel row of `F` whose edge links in `G` is one of `F`'s rigidity rows. Stated taking the
  -- `G.IsLink` as an explicit argument (the membership witness is supplied directly, not inferred),
  -- so the heavy `ofNormals` carrier never enters the elaborator's `whnf` (TACTICS-QUIRKS §38).
  have hrow_mem : ∀ (i : β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k),
      G.IsLink i.1 (ends i.1).1 (ends i.1).2 → F.panelRow ends i ∈ F.rigidityRows := by
    rintro ⟨e', t₁, t₂⟩ hlink
    exact ⟨e', (ends e').1, (ends e').2, hlink,
      annihRow (F.supportExtensor e') t₁ t₂, by
        rw [BodyHingeFramework.hingeRowBlock_apply, Submodule.mem_dualAnnihilator]
        intro x hx
        rw [Submodule.mem_span_singleton] at hx
        obtain ⟨ρ, rfl⟩ := hx
        rw [map_smul, annihRow_apply_self, smul_zero], rfl⟩
  have hmem : ∀ i : s, F.panelRow ends (i : β × _ × _) ∈ F.rigidityRows := fun i =>
    hrow_mem _ (hsupp _ i.2)
  have hcard : screwDim k * (V(G).ncard - 1) ≤ Nat.card s := hscard
  refine ⟨PanelHingeFramework.ofNormals G ends q₁,
    PanelHingeFramework.ofNormals_graph G ends q₁, hgp, ?_,
    PanelHingeFramework.ofNormals_recordsLinks_of_hends G ends q₁ hends, halg⟩
  have hFG : F.graph.vertexSet = V(G) := by
    rw [hF, PanelHingeFramework.toBodyHinge_graph, PanelHingeFramework.ofNormals_graph]
  have hrig₁ := F.isInfinitesimallyRigidOn_vertexSet_of_independent_rigidityRows hLI₁ hmem
    (by rw [hFG]; exact hnev) (by rw [hFG]; exact hcard)
  rw [hFG] at hrig₁
  -- Convert rigidity to rank via W2 + hdef.
  have hne' : F.graph.vertexSet.Nonempty := by rw [hFG]; exact hnev
  have hW2 := F.finrank_span_rigidityRows_of_rigidOn hne' (by rw [hFG]; exact hrig₁)
  have hVncard : F.graph.vertexSet.ncard = V(G).ncard := by rw [hFG]
  have h1 : 1 ≤ V(G).ncard := (Set.ncard_pos (Set.toFinite _)).2 hnev
  rw [hVncard] at hW2
  rw [← hF, hdef, sub_zero]
  zify [h1] at hW2 ⊢
  exact_mod_cast hW2

/-- **Case I realization: the contraction producer** (`lem:case-I-realization`, the N6 composer;
Katoh–Tanigawa 2011 §6.2, eqs. (6.3), (6.6), (6.9), Phase 22a). The capstone of the Case-I
realization layer: from a *fixed* proper rigid subgraph `H` of a simple minimal `0`-dof-graph `G`
(KT Lemma 6.3's case object, `2 ≤ |V(H)|`) with a chosen representative body `r ∈ V(H)`, and the
conditioned induction hypothesis `hIH` (the shape `theorem_55_generic` threads), the strengthened
generic realization motive `HasGenericFullRankRealization k G` holds. Composed with
`hasFullRankRealization_of_generic` this discharges `theorem_55_generic`'s `hcontractGP` premise
(and `theorem_55`'s `hcontract`), the Case-I branch of the Theorem-5.5 reduction.

The composer assembles the green Case-I bricks against the two splice legs KT eq. (6.3) forces — the
rigid block `GH := H` and the surviving-edge subgraph `Gc := G ＼ E(H)`, both `≤ G` (G3b
`couple_geometry_of_isProperRigidSubgraph`), sharing the representative body `r` — and feeds them to
the **block-triangular** coupling
`hasGenericFullRankRealization_of_couple_blockTriangular_ofNormals_set` (design doc §1.14, the
reframing that replaces the undischargeable common-seed splice of the prior asymmetric coupling):

* **`H`-leg (genuine IH extraction).** `H` is simple (`Graph.Simple.mono` from `G.Simple`), minimal
  `0`-dof (`subgraph_minimality` from its rigidity), and smaller (`V(H) ⊂ V(G)`), so the conditioned
  induction hypothesis `hIH` supplies `HasGenericFullRankRealization k H`; the leg-transport brick
  `hasGenericRealization_transport_ends` re-expresses it at the manufactured parent selector `ends`
  (rigid + transversal on `sH := V(H)`). The block-triangular coupling consumes only the `H`-block
  *rows* (the `H`-leg rank polynomial), so the `H`-leg needs **no** complement-isolation equality —
  only its own rigidity on its full vertex set `V(H)`.
* **`G ＼ E(H)`-leg (N4 + the Claim-6.4 *exterior-projected row-independence*).** The contraction
  `G.rigidContract H r` is itself a minimal `0`-dof-graph (N4 `rigidContract_isMinimalKDof`),
  smaller than `G` (`rigidContract_vertexSet_ncard_lt`), and — by the KT Lemma 6.3 case hypothesis
  `hcSimple` (`(G.rigidContract H r).Simple`; G2b makes this the positive `map`-simplicity
  criterion) — simple, so `hIH` supplies its *generic* realization. **The transport of that rank
  across the collapse map to the surviving edges `E(G) ∖ E(H)` is KT Claim 6.4 (eq. (6.5)/(6.9))**,
  the irreducibly research-shaped step (the collapse redirects each surviving edge's endpoints, so
  no green brick converts the relabelled-contraction rank into the surviving-edge rank — the G3a
  finding). It is now **fully discharged** (Phase 22b) by the U4 assembly
  `rigidContract_exterior_rank_transport_htransport`, which *produces* — from the contraction's
  generic IH — the rank-transport witness as a **rank polynomial** `Qc ≠ 0` whose non-roots carry
  **exterior-column-projected row-independence**: at every `Qc`-non-root seed (the Zariski-open
  generic locus of KT eq. (6.9), *not* every general-position seed), the surviving rows are
  `≥ D(|sc|−1)` and independent after projecting away the rigid-block columns `V(H)`
  (`(extProj V(H)).dualMap`) — KT's bottom-right block rank. The `H`-leg's selector alignment
  `hswap`/`hne_ends` (the KT eq. (6.6) placement) is likewise discharged in-proof against the
  canonical `G.endsOf` selector (route (i)'s strengthened-motive link-recording conjunct).

The block-triangular coupling exhibits `D(|V(G)|−1)` independent rigidity rows of the *single*
common framework `ofNormals G ends q₀` — the `H`-block rows (which vanish under the exterior-column
projection, KT's top-right `0`) `⊔` the surviving-edge rows (the projected block) — and reads
rigidity on `V(G)` off the row count via the device-row closure, *at `q₀` itself*; since `q₀` is
general position the strengthened motive holds. **This needs no common placement rigid on both
legs** (the §1.13 impasse the asymmetric coupling could not cross): the device counts independent
*rows*, never rigidity of one framework on a leg at a shared seed.

**Fully green** (Phase 22b, route (i)): there is no longer any green-modulo bundle. KT Claim 6.4 —
the only former modulo-content, the single KT-eq. (6.5)/(6.9) exterior-projected row-independence —
is discharged by the three landed Case-I bricks U3a/U3b/U2 (assembled by the U4 producer
`rigidContract_exterior_rank_transport_htransport`), and the `H`-leg selector alignment by the
strengthened motive's link-recording conjunct. Every step the composer performs is honest, no
`sorry`, no `axiom`, no explicit `h…` hypothesis. -/
theorem PanelHingeFramework.case_I_realization [DecidableEq β] [Finite α] [Finite β] {n k : ℕ}
    (hD : 3 ≤ Graph.bodyBarDim n)
    (G : Graph α β) (hG : G.IsMinimalKDof n 0)
    {H : Graph α β} (hH : H.IsProperRigidSubgraph G n) {r : α} (hr : r ∈ V(H))
    (hVH2 : 2 ≤ V(H).ncard) (hSimple : G.Simple)
    (hcSimple : (G.rigidContract H r).Simple)
    (hIH : ∀ G' : Graph α β, G'.IsMinimalKDof n 0 → 2 ≤ V(G').ncard →
      V(G').ncard < V(G).ncard →
      (G'.Simple → PanelHingeFramework.HasGenericFullRankRealization k n G') ∧
        HasPanelRealization k n G') :
    PanelHingeFramework.HasGenericFullRankRealization k n G := by
  classical
  haveI : NeZero (Graph.bodyHingeMult n) := ⟨by rw [Graph.bodyHingeMult]; omega⟩
  obtain ⟨⟨hle, hKDof⟩, hVH2', hVHss⟩ := hH
  have hHsub : V(H) ⊆ V(G) := hle.vertexSet_mono
  have hVHlt : V(H).ncard < V(G).ncard := Set.ncard_lt_ncard hVHss (Set.toFinite _)
  -- Manufacture the parent endpoint selector from `G` alone via the canonical `endsOf` (G3c-iii-a):
  -- it links every edge (`isLink_endsOf`), exactly the edge-restricted `hends` the body-set generic
  -- coupling needs (the all-`β` form is unsatisfiable for a label type with non-edges).
  haveI : Inhabited α := ⟨r⟩
  set ends := G.endsOf with hendsDef
  have hends : ∀ e u v, G.IsLink e u v → G.IsLink e (ends e).1 (ends e).2 := by
    rw [hendsDef]; exact fun e _ _ h => G.isLink_endsOf h.edge_mem
  have hHprop : H.IsProperRigidSubgraph G n := ⟨⟨hle, hKDof⟩, hVH2', hVHss⟩
  -- (Phase 22b route (i), Commit 4) The `H`-leg's selector-alignment `hswap`/`hne_ends` — formerly
  -- `hbundle` conjuncts — are now *discharged* against the canonical parent selector `ends =
  -- G.endsOf`: `hne_ends` is `endsOf_fst_ne_snd` (a link's two `endsOf`-ends differ in the loopless
  -- `G`), and the leg-`hswap` is the strengthened-motive link-recording conjunct of the IH
  -- realization composed with `endsOf`'s link-recording (`recordsLinks_swap_endsOf`), applied per
  -- leg below. So `hbundle` now carries only the irreducible Claim-6.4 transport `htransport`.
  haveI : G.Loopless := hSimple.toLoopless
  have hne_ends : ∀ e, G.IsLink e (ends e).1 (ends e).2 → (ends e).1 ≠ (ends e).2 :=
    fun e hlink => G.endsOf_fst_ne_snd hlink.edge_mem
  -- The geometric inputs of the coupling for legs `H` / `G ＼ E(H)` sharing `r` (G3b); the cover is
  -- against the *surviving-body* set `sc := (V(G)∖V(H)) ∪ {r}` (its `(V(G)∖V(H))` part alone
  -- complements `V(H)`).
  obtain ⟨hGH, hGc, _, _, _, _, _⟩ :=
    PanelHingeFramework.couple_geometry_of_isProperRigidSubgraph hHprop hr
  -- (Phase 22b route (i), Commit 5 = U4) The contraction leg's KT Claim 6.4 transport `htransport`
  -- — formerly the explicit `hbundle` conjunct — is now *produced* from the contraction's generic
  -- IH by the U4 assembly `rigidContract_exterior_rank_transport_htransport` (U3a alignment ⊕ U3b
  -- exterior-projected rank ⊕ U2 collapse-relabel row reproduction at U1's degenerate placement).
  -- The surviving-edge subgraph `G ＼ E(H) ≤ G`, so the parent selector `ends = G.endsOf` records
  -- its links: a `(G ＼ E(H))`-link is a `G`-link with the same endpoints (`IsSubgraph.isLink_iff`).
  have hendsGc : ∀ e u v, (G.deleteEdges E(H)).IsLink e u v →
      (G.deleteEdges E(H)).IsLink e (ends e).1 (ends e).2 := fun e u v hlink =>
    (Graph.IsSubgraph.isLink_iff hGc hlink.edge_mem).mpr
      (hends e u v ((Graph.IsSubgraph.isLink_iff hGc hlink.edge_mem).mp hlink))
  have hcover : V(G) ⊆ V(H) ∪ ((V(G) \ V(H)) ∪ {r}) := by
    intro x hx
    by_cases hxH : x ∈ V(H)
    · exact Or.inl hxH
    · exact Or.inr (Or.inl ⟨hx, hxH⟩)
  -- (1) The `H`-leg: extract its generic IH and transport it to the parent selector (rigid +
  -- transversal on its *full* `V(H)`). The block-triangular coupling uses only the `H`-block *rows*
  -- (the `H`-leg rank polynomial), so no complement-isolation equality is needed for this leg.
  have hHmin : H.IsMinimalKDof n 0 := Graph.subgraph_minimality hle hG hKDof
  obtain ⟨QH, hQHg, hQHgp, hQHrank, hQHrec, _⟩ :=
    (hIH H hHmin hVH2 hVHlt).1 (hSimple.mono hle)
  -- Derive rigidity from hQHrank (B1.mpr).
  have hHne : V(H).Nonempty := ⟨r, hr⟩
  have hne_QH : QH.toBodyHinge.graph.vertexSet.Nonempty := by
    rw [PanelHingeFramework.toBodyHinge_graph, hQHg]; exact hHne
  rw [hKDof, sub_zero] at hQHrank
  have hVH_eq : QH.toBodyHinge.graph.vertexSet = V(H) := by
    rw [PanelHingeFramework.toBodyHinge_graph, hQHg]
  have h1H : 1 ≤ V(H).ncard := (Set.ncard_pos (Set.toFinite _)).2 hHne
  have hQHrig : QH.toBodyHinge.IsInfinitesimallyRigidOn V(H) := by
    rw [← hVH_eq,
      BodyHingeFramework.isInfinitesimallyRigidOn_vertexSet_iff_finrank_span_rigidityRows
        QH.toBodyHinge hne_QH, hVH_eq]
    zify [h1H] at hQHrank ⊢; exact_mod_cast hQHrank
  -- The `H`-leg `hswap` (U3a, route (i)): the IH realization `QH` records `H`'s links up to swap
  -- (`hQHrec`, the strengthened-motive conjunct), and `endsOf` records `G`'s — so the two selectors
  -- agree on `H`-links up to swap (`recordsLinks_swap_endsOf`). The brick's `hne_ends` is
  -- edge-restricted; an `H`-link's `ends`-endpoints form a `G`-link (`H ≤ G`), where `hne_ends`
  -- (the discharged `endsOf_fst_ne_snd`) applies.
  obtain ⟨qH, hneH, hrigH⟩ :=
    PanelHingeFramework.hasGenericRealization_transport_ends H ends QH hQHg hQHgp hQHrig
      (PanelHingeFramework.recordsLinks_swap_endsOf hle QH.ends hQHrec)
      (fun e he => hne_ends e (he.of_le hle))
  -- (2) The `G ＼ E(H)`-leg: the contraction is a smaller, simple minimal `0`-dof-graph (N4 +
  -- `hcSimple`), so `hIH` supplies its generic realization `Qcf`. KT Claim 6.4 (eqs. (6.5)/(6.9),
  -- now *discharged* by the U4 assembly `rigidContract_exterior_rank_transport_htransport`)
  -- transports that rank across the collapse map to **one** parent seed `q₀` and a subfamily `t` of
  -- surviving-edge links whose **exterior-projected** rows are independent at `q₀` — KT's
  -- bottom-right block rank.
  have hKmin : (G.rigidContract H r).IsMinimalKDof n 0 :=
    Graph.rigidContract_isMinimalKDof hG hHprop hr
  have hKlt : V(G.rigidContract H r).ncard < V(G).ncard :=
    Graph.rigidContract_vertexSet_ncard_lt hHsub hVH2
  have hK2 : 2 ≤ V(G.rigidContract H r).ncard := by
    rw [Graph.rigidContract_vertexSet_ncard hr hHsub]
    have hVHle : V(H).ncard ≤ V(G).ncard := Set.ncard_le_ncard hHsub (Set.toFinite _)
    omega
  have hQcf : PanelHingeFramework.HasGenericFullRankRealization k n (G.rigidContract H r) :=
    (hIH (G.rigidContract H r) hKmin hK2 hKlt).1 hcSimple
  have hKne : V(G.rigidContract H r).Nonempty :=
    (Set.ncard_pos (Set.toFinite _)).mp (by omega)
  obtain ⟨q₀, t, hsupp, hcount, hindep⟩ :=
    PanelHingeFramework.rigidContract_exterior_rank_transport (k := k) G H ends n hKne hKmin.1 hQcf
      (PanelHingeFramework.rigidContract_exterior_rank_transport_htransport G H ends hr hHsub
        hcSimple hKne hKmin.1 hQcf hendsGc)
  -- The bounded `D∘panelRow` packaging (N-22b-2) lifts the single-placement witness `(q₀, t)` to
  -- the contraction **rank polynomial** `Qc ≠ 0` whose non-roots carry exterior-projected
  -- surviving-row independence (the Zariski-open generic locus of KT eq. (6.9), not every GP seed).
  obtain ⟨Qc, hQc_ne, hQc_rat, hsc_proj_indep⟩ :=
    PanelHingeFramework.exists_rankPolynomial_of_rigidOn_linking_set_proj (k := k)
      (G.deleteEdges E(H)) ends V(H) hsupp hcount hindep
  -- (3) Feed both legs into the **block-triangular** body-set generic coupling (`sH := V(H)`,
  -- `sc := (V(G)∖V(H))∪{r}`): the `H`-block rows from the rank polynomial, the surviving-edge
  -- block from the Claim-6.4 exterior-projected row-independence at the `Qc`-non-root seed. The
  -- device-row closure reads rigidity on `V(G)` off the joint row count — no common placement
  -- rigid on both legs. `Qc` is rational (`hQc_rat`), so the shared seed can be taken alg-indep.
  exact PanelHingeFramework.hasGenericFullRankRealization_of_couple_blockTriangular_ofNormals_set
    G ends hends hGH hGc (sH := V(H)) (sc := (V(G) \ V(H)) ∪ {r}) (c := r) hr (Or.inr rfl) hcover
    ⟨r, hHsub hr⟩ ⟨r, hr⟩ le_rfl (qH := qH) hneH hrigH Qc hQc_ne hQc_rat hsc_proj_indep n hG.1

/-- **The device's coordinatization from a spanning enumeration of one realization's rigidity
rows** (`lem:genericity-device`, the route-(a) closure for Case I; Phase 21b). The route-(a)
resolution the hand-off flagged: the witness realization Case I needs is *constructed directly* by
the exterior-algebra existence lemma `exists_independent_panelSupportExtensor` (a basis choice on
`⋀²`, Phase 21/17), not found by perturbing along a path through panel-coordinate space. So the
multivariate family the device consumes can be the **constant** family `F p = F₀`, with `g p = a`
any family whose span lies **inside** the rigidity rows of the single good realization `F₀`
(`hspanrows`, a `≤`); the bilinearity obstruction (the panel rows are quadratic along a real line
through normal-space) never bites, because no path is traversed — the device reads off the corank
`#s` at the one hand-built realization, which is all Case I's block-triangular gluing needs.

This packages the constant family into the multivariate `exists_good_realization`: the
panel-coordinate variables `σ := Unit` are vacuous (the framework does not vary), the polynomial
coordinates are the constants `c i j = C (φ (a i) j)` (so `hg` is `eval_C`), and the
coordinatization `hcoord` is the per-framework `infinitesimalMotions_eq_dualCoannihilator` composed
with the coannihilator anti-monotonicity `dualCoannihilator_anti hspanrows` — which is why
`hspanrows` only needs the `≤` containment, not equality. The basis identification `φ` is taken from
any finite basis of the
finite-dimensional dual `α → ScrewSpace k` (`Module.finBasis … |>.equivFun`). The output is the
unquantified codimension bound `#s + dim Z(F₀) ≤ D|V|` at `F₀` itself — the form
`hglue_of_realization` consumes. The independent subfamily `s` (the engine's `hindep`) is supplied
by `exists_independent_panelSupportExtensor` through the hinge-row block. -/
theorem exists_good_realization_const [Fintype α] {ι : Type*} [Finite ι]
    (F₀ : BodyHingeFramework k α β) (a : ι → Module.Dual ℝ (α → ScrewSpace k))
    (hspanrows : Submodule.span ℝ (Set.range a) ≤ Submodule.span ℝ F₀.rigidityRows)
    {s : Set ι} (hindep : LinearIndependent ℝ (fun i : s => a i)) :
    Nat.card s + Module.finrank ℝ F₀.infinitesimalMotions ≤ screwDim k * Fintype.card α := by
  classical
  set n := Module.finrank ℝ (Module.Dual ℝ (α → ScrewSpace k)) with hn
  -- A basis identification of the finite-dimensional dual with `Fin n → ℝ`.
  let φ : Module.Dual ℝ (α → ScrewSpace k) ≃ₗ[ℝ] (Fin n → ℝ) :=
    (Module.finBasis ℝ (Module.Dual ℝ (α → ScrewSpace k))).equivFun
  -- The constant family: `F p = F₀`, rows `g p = a`, polynomial coords the constants `φ (a i) j`.
  -- The `hcoord` leg needs only `span (range a) ⊆ span rigidityRows`: anti-monotonicity of the
  -- coannihilator (`dualCoannihilator_anti`) reverses it onto `infinitesimalMotions` rewritten as
  -- `(span rigidityRows).dualCoannihilator`, so the spanning hypothesis can be a `≤`.
  have hcoord : ∀ _ : Unit → ℝ, F₀.infinitesimalMotions
      ≤ (Submodule.span ℝ (Set.range a)).dualCoannihilator := fun _ => by
    rw [F₀.infinitesimalMotions_eq_dualCoannihilator]
    exact Submodule.dualCoannihilator_anti hspanrows
  obtain ⟨p, hp⟩ := exists_good_realization (σ := Unit) (s := s) (p₀ := fun _ => 0)
    (fun _ => F₀) (fun _ => a) (fun i j => MvPolynomial.C (φ (a i) j)) φ
    (fun _ i j => by rw [MvPolynomial.eval_C]) hcoord hindep
  exact hp

/-- **Realization producer from a fixed-framework independent rigidity-row-span family** (C1;
`lem:case-III` / `lem:case-II-realization`, the genericity-free device-feed variant; Katoh–Tanigawa
2011 §6.4.1 eqs. (6.24)–(6.44), Phase 22g). The fixed-framework analog of
`hasFullRankRealization_of_independent_panelRow` for a *non-panelRow* family: given the concrete
free-normal framework `F₀ = ofNormals G ends q₀` over a nonempty body set `V(G)` (`hne`), an
independent family `f : ι → Module.Dual` whose span lies inside
the rigidity rows of `F₀` (`hsub`, weaker than panelRow membership) and that meets the relative
target count `D(|V(G)|−1) ≤ |ι|` (`hcard`), then `G` has a full-rank panel realization
`HasFullRankRealization k G` — witnessed by `F₀` **itself**, no genericity round-trip.

The realization motive `HasFullRankRealization k G := ∃ Q, Q.graph = G ∧ …IsInfinitesimallyRigidOn
V(G)` asks for *some* rigid framework, not a generic one, so the candidate completion uses the fixed
placement `F₀` directly. The proof reads rigidity off the span-containment core
`isInfinitesimallyRigidOn_vertexSet_of_span_le_rigidityRows` (the rank-nullity argument: the
independent span-into-rigidity-rows family of count `≥ D(|V|−1)` caps the null space at the
relative full dimension, N3), so unlike the panelRow feed it needs **no** `annihRowPoly`
coordinatization of the rows — the candidate `d = 3` `+1` row `hingeRow v b r̂` is a combination of
`e_b`-panel rows, in `span rigidityRows` but not a single panelRow (design doc §1.35), exactly the
shape `hsub` admits. This is the keystone the corrected `d = 3` candidate-completion route turns on
(C2/C3). -/
theorem PanelHingeFramework.hasFullRankRealization_of_independent_rigidityRow
    [Finite α] [Finite β] (G : Graph α β) (ends : β → α × α) (hne : V(G).Nonempty)
    {q₀ : α × Fin (k + 2) → ℝ} {ι : Type*} [Finite ι]
    {f : ι → Module.Dual ℝ (α → ScrewSpace k)} (hLI : LinearIndependent ℝ f)
    (hsub : Submodule.span ℝ (Set.range f)
      ≤ Submodule.span ℝ (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.rigidityRows)
    (hcard : screwDim k * (V(G).ncard - 1) ≤ Nat.card ι) :
    PanelHingeFramework.HasFullRankRealization k G := by
  set F := (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge with hF
  have hG : F.graph.vertexSet = V(G) := rfl
  refine ⟨PanelHingeFramework.ofNormals G ends q₀,
    PanelHingeFramework.ofNormals_graph G ends q₀, ?_⟩
  have hrig := F.isInfinitesimallyRigidOn_vertexSet_of_span_le_rigidityRows hLI hsub
    (by rw [hG]; exact hne) (by rw [hG]; exact hcard)
  rw [hG] at hrig
  exact hrig

/-- **C2 — the single-candidate brick** (`lem:case-III` / `lem:case-II-realization`, the
per-candidate selector → realization step of the `d = 3` `hsplit` producer; Katoh–Tanigawa 2011
§6.4.1 eqs. (6.27)–(6.44), Phase 22g). Turns one candidate's *row-space selector* — the conditional
`r̂(C(e)) ≠ 0 → LinearIndependent fam` that the candidate-completion producers
(`linearIndependent_sum_{p2,p3,augment}_candidateRow`) supply — plus per-row membership in the fixed
realization's rigidity rows and the relative-full count `D(|V(G)|−1) ≤ |κ|` into the realization
conclusion `r̂(C(e)) ≠ 0 → HasFullRankRealization k G`, by feeding C1
(`hasFullRankRealization_of_independent_rigidityRow`) at the fixed placement `ofNormals G ends q₀`.

This is the corrected device feed (`notes/Phase22-realization-design.md` §1.35): the candidate's
`+1` row `hingeRow v b r̂` is provably **not** a single `panelRow` (it has `r̂(C(e_b)) ≠ 0`, while
every panelRow annihilates its edge's extensor), so the panelRow-shaped genericity feed
(`hasFullRankRealization_of_independent_panelRow_index`) does not apply; but the row IS a
combination of `e_b`-panelRows, hence in `span rigidityRows`, exactly the `hmem`/C1 shape. The span
containment C1 needs is assembled from the pointwise membership `hmem` (`Submodule.span_le` over
`Set.range`), so the consumer (C3) supplies only the per-summand `rigidityRows` membership — the
OLD/NEW panel-row blocks via `panelRow_mem_rigidityRows`/L4, the `r̂`-row via its `e_b`-panelRow
decomposition. The selector `hsel` is consumed at the producer's witness line (the row-space
criterion at `C(L) = pᵢ ∨ pⱼ`, Leaf 2/3); the brick is graph-free except the concrete `ofNormals`
carrier C1 fixes (TACTICS-QUIRKS §38). -/
theorem PanelHingeFramework.hasFullRankRealization_of_candidateSelector
    [Finite α] [Finite β] (G : Graph α β) (ends : β → α × α) (hne : V(G).Nonempty)
    {q₀ : α × Fin (k + 2) → ℝ} {κ : Type*} [Finite κ]
    {fam : κ → Module.Dual ℝ (α → ScrewSpace k)}
    {r : Module.Dual ℝ (ScrewSpace k)} {C : ScrewSpace k}
    (hsel : r C ≠ 0 → LinearIndependent ℝ fam)
    (hmem : ∀ i, fam i ∈ Submodule.span ℝ
      (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.rigidityRows)
    (hcard : screwDim k * (V(G).ncard - 1) ≤ Nat.card κ) :
    r C ≠ 0 → PanelHingeFramework.HasFullRankRealization k G := by
  intro hr
  refine PanelHingeFramework.hasFullRankRealization_of_independent_rigidityRow G ends hne
    (q₀ := q₀) (hsel hr) ?_ hcard
  rw [Submodule.span_le, Set.range_subset_iff]
  exact fun i => hmem i

/-- **Case I `hglue` from a single panel realization** (`lem:case-I`, the route-(a) capstone;
Katoh–Tanigawa 2011 §6.1 Claim 6.4). The genuinely-consumer-facing form of the genericity device
for Case I: given a single body-hinge realization `F₀`, a finite family `a` of functionals
**spanning** its rigidity rows (`hspanrows`), a linearly independent subfamily indexed by `s`
(`hindep`, the witnessed corank, supplied by `exists_independent_panelSupportExtensor` through the
hinge-row block), and the **rank-match** `hmatch` — the witnessed corank `#s` equals the
contraction's inductive rank `D(|V|−1) − dim Z_s` — the block-triangular gluing inequality
`hglue : dim Z(G,p) ≤ D + dim Z_s` holds at `F₀` itself.

This is the route-(a) resolution promised in the hand-off: the bilinearity obstruction (panel rows
quadratic along a real line) is sidestepped because the witness realization `F₀` is *constructed*
by the exterior-algebra existence lemma rather than reached by perturbation, so the device runs on
the **constant** multivariate family `F p = F₀` (`exists_good_realization_const`), reading off the
corank `#s` at `F₀`. The arithmetic then substitutes `#s = D(|V|−1) − dim Z_s` (`hmatch`) into the
device's `#s + dim Z(F₀) ≤ D|V|`, collapsing `D|V| − (D(|V|−1) − dim Z_s)` to `D + dim Z_s` via
`D·(|V|−1) = D·|V| − D`. The residual per-consumer work is now purely combinatorial-geometric:
exhibit, from the contraction realization plus the rigidly placed block `V(H)`, the single
realization `F₀`, a finite spanning row family `a`, and the independent subfamily `s` whose size
matches `#s = D(|V|−1) − dim Z_s` (`hspanrows` + `hindep` + `hmatch`); no path construction remains.
It bottoms on `screwDim k * (|V|−1) = D|V| − D`, the trivial-motion codimension
`lem:trivial-motions-rank-bound`. -/
theorem hglue_of_realization [Fintype α] [Nonempty α] {ι : Type*} [Finite ι]
    (F₀ : BodyHingeFramework k α β) (a : ι → Module.Dual ℝ (α → ScrewSpace k))
    {s : Set ι} {sblk : Set α}
    (hspanrows : Submodule.span ℝ (Set.range a) = Submodule.span ℝ F₀.rigidityRows)
    (hindep : LinearIndependent ℝ (fun i : s => a i))
    (hmatch : Nat.card s + Module.finrank ℝ F₀.infinitesimalMotions ≤ screwDim k * Fintype.card α →
      (Nat.card s : ℤ) = screwDim k * (Fintype.card α - 1)
        - Module.finrank ℝ (F₀.pinnedMotionsOn sblk)) :
    (Module.finrank ℝ F₀.infinitesimalMotions : ℤ) ≤
      screwDim k + Module.finrank ℝ (F₀.pinnedMotionsOn sblk) := by
  have ht := exists_good_realization_const F₀ a hspanrows.le hindep
  have hcard : 1 ≤ Fintype.card α := Fintype.card_pos
  have hmatch' := hmatch ht
  have ht' : (Nat.card s : ℤ) + Module.finrank ℝ F₀.infinitesimalMotions
      ≤ screwDim k * Fintype.card α := by exact_mod_cast ht
  -- `D·(|V|−1) = D·|V| − D`, so substituting `#s` collapses the bound to `D + dim Z_s`.
  rw [Nat.cast_sub hcard, Nat.cast_one, mul_sub, mul_one] at hmatch'
  omega

/-- **Case I `hglue` from an independent rigidity-row family** (`lem:case-I`, the route-(a)
capstone in its consumer-ready form; Katoh–Tanigawa 2011 §6.1 Claim 6.4, Phase 21b). The bridge
that feeds the **assembled** independent rigidity-row family of
`exists_independent_rigidityRows_of_forest` directly into the block-triangular gluing inequality,
discharging `hglue_of_realization`'s finite-spanning-family `a` and its independent-subfamily index
`s` once and for all.

`hglue_of_realization` is stated against a single finite family `a` that *spans* `F₀.rigidityRows`
together with an independent subfamily indexed by `s ⊆ ι` of `a` itself. The Case-I assembly,
however, produces its independent family `r : κ → Dual` (the `(D−1)·|J|` rows of a rigid block's
spanning forest of transversal hinges) as members of `F₀.rigidityRows` — *not* as a syntactic
subfamily of any pre-chosen spanning enumeration. This lemma closes that index gap with the
**concatenation** `a := Sum.elim r a₀`, where `a₀` is any finite family spanning the rigidity rows
(`exists_finite_spanning_rigidityRows`): its range is `range r ∪ range a₀`, and since `range r ⊆
span F₀.rigidityRows = span (range a₀)`, the concatenated family still spans the rigidity rows
(`hspanrows`); the subfamily indexed by `s := range Sum.inl` is exactly `r` (independent by
`hr`, transported across the `Sum.inl` reindexing). The corank then matches `Nat.card κ` (the
forest's `(D−1)·|J|`), so the route-(a) capstone fires with `hmatch` keyed to `κ` rather than to a
hand-chosen subset of an enumeration.

The residual per-consumer obligations are now exactly two and *both purely geometric*: (i) exhibit
the realization `F₀` (a `PanelHingeFramework`-via-`toBodyHinge` from the contraction realization
plus the rigidly placed block `V(H)`), supplying the forest data `r` via
`exists_independent_rigidityRows_of_forest`; and (ii) the count match `hmatch`
(`Nat.card κ = D(|V|−1) − dim Z_s`) against the contraction's inductive `RankHypothesis`. No
spanning-family construction, no subfamily-index bookkeeping, and no affine path remain. -/
theorem hglue_of_independent_rigidityRows [Fintype α] [Nonempty α] {κ : Type*} [Finite κ]
    (F₀ : BodyHingeFramework k α β) {sblk : Set α}
    (r : κ → Module.Dual ℝ (α → ScrewSpace k)) (hr : LinearIndependent ℝ r)
    (hmem : ∀ i, r i ∈ Submodule.span ℝ F₀.rigidityRows)
    (hmatch : Nat.card κ + Module.finrank ℝ F₀.infinitesimalMotions ≤ screwDim k * Fintype.card α →
      (Nat.card κ : ℤ) = screwDim k * (Fintype.card α - 1)
        - Module.finrank ℝ (F₀.pinnedMotionsOn sblk)) :
    (Module.finrank ℝ F₀.infinitesimalMotions : ℤ) ≤
      screwDim k + Module.finrank ℝ (F₀.pinnedMotionsOn sblk) := by
  classical
  -- A finite family `a₀` spanning the rigidity rows; concatenate `r` in front of it.
  obtain ⟨n, a₀, ha₀⟩ := F₀.exists_finite_spanning_rigidityRows
  set a : κ ⊕ Fin n → Module.Dual ℝ (α → ScrewSpace k) := Sum.elim r a₀ with ha
  -- The concatenated family still spans the rigidity rows: `range r ⊆ span (range a₀)`.
  have hspanrows : Submodule.span ℝ (Set.range a) = Submodule.span ℝ F₀.rigidityRows := by
    rw [ha, Set.Sum.elim_range, Submodule.span_union, ha₀]
    refine le_antisymm (sup_le ?_ le_rfl) le_sup_right
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe]; exact ha₀ ▸ hmem i
  -- The subfamily indexed by `range Sum.inl` is exactly `r`, hence independent.
  have hindep : LinearIndependent ℝ
      (fun i : (Set.range (Sum.inl : κ → κ ⊕ Fin n)) => a i) := by
    have hcomp : (fun i : (Set.range (Sum.inl : κ → κ ⊕ Fin n)) => a (i : κ ⊕ Fin n))
        = r ∘ (fun i => (Set.rangeSplitting Sum.inl i : κ)) := by
      funext i
      have := Set.apply_rangeSplitting (Sum.inl : κ → κ ⊕ Fin n) i
      rw [ha]
      simp only [Function.comp_apply]
      rw [show (i : κ ⊕ Fin n) = Sum.inl (Set.rangeSplitting Sum.inl i) from this.symm,
        Sum.elim_inl]
    rw [hcomp]
    exact hr.comp _ (Set.rangeSplitting_injective (Sum.inl : κ → κ ⊕ Fin n))
  -- The corank `#s = Nat.card (range Sum.inl) = Nat.card κ`.
  have hcard : Nat.card (Set.range (Sum.inl : κ → κ ⊕ Fin n)) = Nat.card κ := by
    rw [Nat.card_range_of_injective Sum.inl_injective]
  refine hglue_of_realization F₀ a (s := Set.range (Sum.inl : κ → κ ⊕ Fin n)) (sblk := sblk)
    hspanrows hindep ?_
  rw [hcard]; exact hmatch

/-- **Case I `hglue` from a rigid block's spanning forest** (`lem:case-I`, the route-(a) capstone
in its fully geometry-facing form; Katoh–Tanigawa 2011 §6.1 Claim 6.4, §6.2/6.5, Phase 21b). The
last reduction of the route-(a) chain before the genuinely-geometric `F₀` exhibition: it composes
the assembled forest family `exists_independent_rigidityRows_of_forest` (the rigid block's
`(D−1)·|J|` independent rigidity rows, indexed by `Σ _ : J, Fin (screwDim k − 1)`) straight into
the consumer bridge `hglue_of_independent_rigidityRows`, so the only remaining consumer obligation
is the *forest data itself* plus the count.

Concretely: given a single body-hinge realization `F₀` whose rigid block `V(H) = s_blk` carries a
spanning forest of transversal hinges — each hinge `e j` oriented from a *private endpoint* `u j`
(the forest child, `u` injective) to an arbitrary `other j`, with the forest-separation hypothesis
`hsep : ∀ j j', other j ≠ u j'` and every hinge transversal (`he : F₀.supportExtensor (e j) ≠ 0`)
— the block-triangular gluing inequality `hglue : dim Z(G,p) ≤ D + dim Z_s` holds at `F₀`, provided
only the **count match** `hmatch`: the forest's row count `|J|·(D−1)` equals the contraction's
inductive rank `D(|V|−1) − dim Z_s`. The forest rows discharge `hglue_of_independent_rigidityRows`'s
independent family `r` (via `linearIndependent_hingeRow_forest`) and its membership obligation
(each row is in `F₀.rigidityRows` by the hinge link `hlink j`); the cardinality
`Nat.card (Σ _ : J, Fin (screwDim k − 1)) = |J|·(D−1)` (`Nat.card_sigma`) keys `hmatch` to the
forest size.

This is the last *generic* (graph-and-hinge-agnostic) reduction. The remaining consumer work — the
genuinely-geometric Case-I assembly (KT §6.2/6.5) — is to exhibit, from the contraction realization
`G/E(H)` at its inductive `RankHypothesis` plus the rigidly placed block `V(H)`, the single
realization `F₀` (a `PanelHingeFramework`-via-`toBodyHinge`), the private-endpoint spanning forest
`u`/`other`/`e` of `V(H)`'s transversal hinges (transversality from
`exists_independent_panelSupportExtensor` general position), and the count `hmatch` against the
contraction's inductive rank. -/
theorem hglue_of_forest [Fintype α] [Nonempty α] {J : Type*} [Finite J]
    (F₀ : BodyHingeFramework k α β) {sblk : Set α}
    {u other : J → α} {e : J → β} (hu : Function.Injective u)
    (hsep : ∀ j j', other j ≠ u j') (hlink : ∀ j, F₀.graph.IsLink (e j) (u j) (other j))
    (he : ∀ j, F₀.supportExtensor (e j) ≠ 0)
    (hmatch : Nat.card J * (screwDim k - 1) + Module.finrank ℝ F₀.infinitesimalMotions
        ≤ screwDim k * Fintype.card α →
      (Nat.card J * (screwDim k - 1) : ℤ) = screwDim k * (Fintype.card α - 1)
        - Module.finrank ℝ (F₀.pinnedMotionsOn sblk)) :
    (Module.finrank ℝ F₀.infinitesimalMotions : ℤ) ≤
      screwDim k + Module.finrank ℝ (F₀.pinnedMotionsOn sblk) := by
  classical
  haveI : Fintype J := Fintype.ofFinite J
  obtain ⟨r, hr, hmem⟩ := F₀.exists_independent_rigidityRows_of_forest hu hsep hlink he
  -- `Nat.card (Σ _ : J, Fin (screwDim k − 1)) = |J|·(D − 1)`.
  have hcard : Nat.card ((_ : J) × Fin (screwDim k - 1)) = Nat.card J * (screwDim k - 1) := by
    simp [Nat.card_eq_fintype_card]
  refine hglue_of_independent_rigidityRows F₀ r hr
    (fun p => Submodule.subset_span (hmem p)) (sblk := sblk) ?_
  rw [hcard]; exact hmatch

/-- **Case I panel capstone: a general-position rigid block realizes the rank** (`lem:case-I`, the
route-(a) panel-layer iff-realization; Katoh–Tanigawa 2011 §6.1 Claim 6.4, §6.2/6.5, Phase 21b).
The packaging of `hglue_of_forest` against a *panel*-hinge framework `P` whose normals are in
general position (`P.IsGeneralPosition`, e.g. the moment-curve assignment
`isGeneralPosition_withMomentNormals`): it sources the per-hinge transversality input `he` of
`hglue_of_forest` from the general position via `supportExtensor_ne_zero_of_isGeneralPosition`,
leaving the consumer only the *graph* data of the rigid block's spanning forest and the count.

Concretely, for the body-hinge interpretation `P.toBodyHinge` on a (nonempty) rigid block
`s = sblk` carrying a spanning forest of hinges — each `e j` linking a *private endpoint* `u j`
(the forest child, `u` injective) to an arbitrary `other j`, with the forest-separation hypothesis
`hsep : ∀ j j', other j ≠ u j'` and each hinge's panel endpoints matching its forest orientation
(`hends : P.ends (e j) = (u j, other j)`) — the framework realizes the target rank at `k'`
(`RankHypothesis k'`, i.e. `dim Z(G,p) = D + k'`) **iff** the block pin `pinnedMotionsOn s` has
dimension `k'`, the contraction's inductive rank, provided the **count match** `hmatch`: the
forest's row count `|J|·(D−1)` equals `D(|V|−1) − dim Z_s`. Endpoint distinctness of each forest
hinge — the input `supportExtensor_ne_zero_of_isGeneralPosition` needs — is read off the
forest separation at the diagonal (`(hsep j j) : other j ≠ u j`, so `(P.ends (e j)).1 = u j ≠
other j = (P.ends (e j)).2` through `hends`), so no extra transversality hypothesis is required:
general position of the panel normals discharges every forest hinge at once.

This is the last reduction of the Case-I route-(a) chain that still mentions the panel general
position: it composes `hglue_of_forest` (the rigid block's `(D−1)·|J|` independent rigidity rows
feeding the block-triangular gluing) with `supportExtensor_ne_zero_of_isGeneralPosition` (every
forest hinge transversal under general position) into `toBodyHinge_rankHypothesis_iff_finrank_
pinnedMotionsOn`. The remaining consumer work — the genuinely-geometric Case-I assembly (KT
§6.2/6.5) — is the *graph-and-realization* exhibition: build `P` (a `PanelHingeFramework`, its
normals from `withMomentNormals` on an injective parameter map, so `IsGeneralPosition` for free) on
the parent graph `G` from the contraction realization `G/E(H)` plus the rigidly placed block
`V(H)`, exhibit the block's spanning forest `u`/`other`/`e` (with `hends` by construction), and
discharge the count `hmatch` against the contraction's inductive `RankHypothesis`. -/
theorem PanelHingeFramework.toBodyHinge_rankHypothesis_iff_pinnedMotionsOn_of_generalPosition
    [Fintype α] [Nonempty α] {J : Type*} [Finite J]
    (P : PanelHingeFramework k α β) (hP : P.IsGeneralPosition)
    {sblk : Set α} (hs : sblk.Nonempty) (k' : ℤ)
    {u other : J → α} {e : J → β} (hu : Function.Injective u)
    (hsep : ∀ j j', other j ≠ u j') (hlink : ∀ j, P.toBodyHinge.graph.IsLink (e j) (u j) (other j))
    (hends : ∀ j, P.ends (e j) = (u j, other j))
    (hmatch : Nat.card J * (screwDim k - 1) + Module.finrank ℝ P.toBodyHinge.infinitesimalMotions
        ≤ screwDim k * Fintype.card α →
      (Nat.card J * (screwDim k - 1) : ℤ) = screwDim k * (Fintype.card α - 1)
        - Module.finrank ℝ (P.toBodyHinge.pinnedMotionsOn sblk)) :
    P.toBodyHinge.RankHypothesis k' ↔
      (Module.finrank ℝ (P.toBodyHinge.pinnedMotionsOn sblk) : ℤ) = k' := by
  have he : ∀ j, P.toBodyHinge.supportExtensor (e j) ≠ 0 := fun j =>
    P.supportExtensor_ne_zero_of_isGeneralPosition hP (e := e j)
      (by rw [hends j]; exact (hsep j j).symm)
  exact P.toBodyHinge_rankHypothesis_iff_finrank_pinnedMotionsOn hs k'
    (hglue_of_forest P.toBodyHinge hu hsep hlink he hmatch)

/-- **Case I from-scratch realization entry point: a moment-curve framework realizes the rank**
(`lem:case-I`, the route-(a) panel-layer iff-realization specialized to the `ofParam` constructor;
Katoh–Tanigawa 2011 §6.1 Claim 6.4, §6.2/6.5, Phase 21b). The packaging of the general-position
capstone `toBodyHinge_rankHypothesis_iff_pinnedMotionsOn_of_generalPosition` against the
from-scratch framework `ofParam G ends param` built directly on the parent multigraph `G`, its
hinge-endpoint selector `ends`, and an *injective* real parameter map `param`. Because the
moment-curve normals at an injective `param` are automatically in general position
(`isGeneralPosition_ofParam`), the per-hinge transversality input is discharged for free, and the
endpoint hypothesis `hends` of the capstone reduces to a statement about `ends` *directly*
(`ofParam_ends` is definitional).

Concretely, for the body-hinge interpretation `(ofParam G ends param).toBodyHinge` on a (nonempty)
rigid block `s = sblk` carrying a spanning forest of hinges — each `e j` linking a *private
endpoint* `u j` (the forest child, `u` injective) to an arbitrary `other j`, with the
forest-separation `hsep : ∀ j j', other j ≠ u j'`, each hinge a genuine link of `G`
(`hlink : G.IsLink (e j) (u j) (other j)`), and the endpoint selector matching the forest
orientation (`hends : ∀ j, ends (e j) = (u j, other j)`) — the framework realizes the target rank
at `k'` (`RankHypothesis k'`, i.e. `dim Z(G,p) = D + k'`) **iff** the block pin `pinnedMotionsOn s`
has dimension `k'`, provided the **count match** `hmatch` (`|J|·(D−1) = D(|V|−1) − dim Z_s`). This
is the realization-side entry point of the genuinely-geometric Case-I assembly (KT §6.2/6.5):
combinatorial inputs `(G, ends)` carry the geometry of the rigid-subgraph contraction
`G/E(H) ⊔ V(H)`, the forest data `u`/`other`/`e` is read off the rigid block, and the genericity is
the single injective real assignment `param`. The remaining consumer obligation is purely
combinatorial — exhibit the parent graph `G`, its endpoint selector `ends`, the block's spanning
forest, and discharge the count `hmatch` against the contraction's inductive `RankHypothesis`. -/
theorem PanelHingeFramework.ofParam_rankHypothesis_iff_pinnedMotionsOn
    [Fintype α] [Nonempty α] {J : Type*} [Finite J]
    (G : Graph α β) (ends : β → α × α) {param : α → ℝ} (hparam : Function.Injective param)
    {sblk : Set α} (hs : sblk.Nonempty) (k' : ℤ)
    {u other : J → α} {e : J → β} (hu : Function.Injective u)
    (hsep : ∀ j j', other j ≠ u j')
    (hlink : ∀ j, G.IsLink (e j) (u j) (other j))
    (hends : ∀ j, ends (e j) = (u j, other j))
    (hmatch : Nat.card J * (screwDim k - 1)
        + Module.finrank ℝ (ofParam (k := k) G ends param).toBodyHinge.infinitesimalMotions
        ≤ screwDim k * Fintype.card α →
      (Nat.card J * (screwDim k - 1) : ℤ) = screwDim k * (Fintype.card α - 1)
        - Module.finrank ℝ
            ((ofParam (k := k) G ends param).toBodyHinge.pinnedMotionsOn sblk)) :
    (ofParam (k := k) G ends param).toBodyHinge.RankHypothesis k' ↔
      (Module.finrank ℝ
        ((ofParam (k := k) G ends param).toBodyHinge.pinnedMotionsOn sblk) : ℤ) = k' :=
  ((ofParam (k := k) G ends param).toBodyHinge_rankHypothesis_iff_pinnedMotionsOn_of_generalPosition
    (isGeneralPosition_ofParam G ends hparam) hs k' hu hsep
    (by simpa using hlink) (by simpa using hends) hmatch)

/-! ### Retired absolute-motive Case-I producers (Phase 21b re-plan)

The four `HasFullRankRealization` producers that lived here —
`hasFullRankRealization_ofParam_of_pinnedMotionsOn`,
`hasFullRankRealization_ofParam_of_isInfinitesimallyRigid`,
`hasFullRankRealization_ofParam_of_contraction`, and
`hasFullRankRealization_of_pinnedMotionsOn` — produced the *absolute* realization motive
`RankHypothesis 0` (`IsInfinitesimallyRigid`, constancy on all of `α`). A 2026-06-04 spike found
that motive unsatisfiable for the non-spanning inductive subgraphs the realization induction
reduces to (a body in `α ∖ V(G)` is a free non-trivial motion), so the producers were green only
over unsatisfiable hypotheses (`hpin`/`hHrig`/`hcrig` over `withGraph`-subgraphs rigid on the whole
`α`). They are retired here as the realization motive (`HasFullRankRealization`) is relativized to
`IsInfinitesimallyRigidOn V(G)`; the genuine device-direct producers (`lem:case-I-realization`,
`lem:case-II-realization`, built on the splice seed + B0 + the green genericity device) replace
them and remain red — see `notes/Phase21b.md` *Hand-off*. The accounting iffs
(`ofParam_rankHypothesis_iff_pinnedMotionsOn` and the nullity `RankHypothesis` chain) are retained
above. -/

/-- **The seed-rank bridge: rigidity at one seed transfers to every algebraically-independent
seed** (`lem:case-III-seed-rank-bridge`, the analytic kernel of KT Claim~6.11; Katoh–Tanigawa 2011
§6.4.1, footnote 6, eqs. (6.18)/(6.22), Phase 22d). If the free-normal panel framework
`ofNormals G ends q₀` is infinitesimally rigid on `V(G)` at *some* seed `q₀` (transversal hinges
`hne`, link-recording selector `hends`), then it is infinitesimally rigid on `V(G)` at *any* seed
`q` that is algebraically independent over `ℚ` (`halg`).

This is the kernel KT's footnote 6 supplies for the nested induction (eq. (6.22)): the inductively-
fixed realization is taken with algebraically-independent coordinates, so the *given* seed —
not merely *some* generic seed — attains the maximal (matroid-predicted) rank of the subgraph. At
the `0`-dof level it is precisely eq. (6.18): the split-off graph `G_v^{ab}` is `0`-dof, so its
generic realization is rigid, and this brick certifies the inductively-fixed seed is rigid for it
too. The three-step composition is the green Phase-22d machinery: the rank polynomial of the rigid
leg (`exists_rankPolynomial_of_rigidOn`) is rational (`Q.coeffs ⊆ range (algebraMap ℚ ℝ)`); the
algebraically-independent seed `q` is a non-root of every nonzero rational polynomial
(`MvPolynomial.eval_ne_zero_of_coeffs_subset_range_of_algebraicIndependent`, footnote 6); and the
device consumer (`isInfinitesimallyRigidOn_ofNormals_of_rankPolynomial_ne_zero`) reads rigidity off
that non-root.

It is honest per the producer-scrutiny gate: the hypothesis `hrig` is rigidity at an *unrelated*
seed `q₀` (the existence of a rigid realization, KT's `0`-dof premise), not rigidity at the target
seed `q` it concludes; the alg-independence of `q` is the genuine new content (footnote 6's standing
inductive choice), and is the conjunct `HasGenericFullRankRealization` carries. -/
theorem PanelHingeFramework.isInfinitesimallyRigidOn_ofNormals_of_algebraicIndependent
    [Finite α] [Finite β] (G : Graph α β) (ends : β → α × α)
    (hends : ∀ e, G.IsLink e (ends e).1 (ends e).2)
    {q₀ : α × Fin (k + 2) → ℝ}
    (hne : ∀ e, (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.supportExtensor e ≠ 0)
    (hnev : V(G).Nonempty)
    (hrig : (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.IsInfinitesimallyRigidOn V(G))
    {q : α × Fin (k + 2) → ℝ} (halg : AlgebraicIndependent ℚ q) :
    (PanelHingeFramework.ofNormals G ends q).toBodyHinge.IsInfinitesimallyRigidOn V(G) := by
  -- (1) The rigid leg at `q₀` carries a rational rank polynomial `Q` (nonzero at `q₀`).
  obtain ⟨s, Q, hcard, hQ₀, hQrat, hQ⟩ :=
    PanelHingeFramework.exists_rankPolynomial_of_rigidOn G ends hends hne hnev hrig
  have hQne : Q ≠ 0 := fun h => hQ₀ (by rw [h, map_zero])
  -- (2) Footnote 6: an alg-indep-over-`ℚ` seed is a non-root of every nonzero rational polynomial.
  have hq : MvPolynomial.eval q Q ≠ 0 :=
    MvPolynomial.eval_ne_zero_of_coeffs_subset_range_of_algebraicIndependent halg hQrat hQne
  -- (3) The device consumer reads rigidity off the non-root `q`.
  exact PanelHingeFramework.isInfinitesimallyRigidOn_ofNormals_of_rankPolynomial_ne_zero
    G ends hnev hends hcard hQ hq

/-- **The eq. (6.22) rank upper bound transferred to every algebraically-independent seed**
(`lem:case-III-seed-rank-bridge` infra, the `def > 0` half of KT Claim~6.11's nested-IH step;
Katoh–Tanigawa 2011 §6.4.1, footnote 6, eq. (6.22), Phase 22d). The seed-rank bridge
(`isInfinitesimallyRigidOn_ofNormals_of_algebraicIndependent`) transfers *full* rigidity
(`def = 0`, eq. (6.18)); KT eq. (6.22) needs the `def > 0` counterpart, the upper bound on the null
space `dim Z(G_v, q) ≤ D|α| − (D(|V_v|−1) − k')` at the inductively-fixed
(algebraically-independent) seed `q`, so that — paired with the genericity-free lower bound
`D + def ≤ dim Z`
(`rigidityMatrix_prop11`'s `hub`) — the nested-IH subgraph `G_v` attains exactly
`RankHypothesis k'`. This lemma is that upper-bound brick, stated in the rank-polynomial-witness
form: a rational rank polynomial `Q` (`hQrat`) whose non-roots witness an independent
`panelRow`-subfamily `s` of `ofNormals G ends ·` (`hQ`), whose edges link in `G` (`hsupp`), bounds
the null space of `ofNormals G ends q` at *any* algebraically-independent-over-`ℚ` seed `q`
(`halg`) by `dim Z ≤ D|α| − #s`.

The transfer is the green Phase-22d machinery: `Q` being rational and nonzero, an algebraically-
independent seed is a non-root
(`MvPolynomial.eval_ne_zero_of_coeffs_subset_range_of_algebraicIndependent`,
footnote 6), so `hQ` gives the size-`#s` independent subfamily *at `q` itself*; the rank-nullity
count (each panel row of `s` lies in the rigidity rows via `hsupp`, so `#s ≤ finrank (span
rigidityRows) = D|α| − dim Z`) then bounds the null space. Honest per the producer-scrutiny gate:
the input is the *polynomial witness* `Q` of an unrelated rigid seed's rank (the eq. (6.18)/(6.22)
producer's output), not the rank concluded; the alg-independence of `q` is the genuine new content
footnote 6 supplies. -/
theorem PanelHingeFramework.finrank_infinitesimalMotions_le_of_rankPolynomial_algebraicIndependent
    [Finite α] [Finite β] (G : Graph α β) (ends : β → α × α)
    {s : Set (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k)}
    {Q : MvPolynomial (α × Fin (k + 2)) ℝ}
    (hsupp : ∀ i ∈ s, G.IsLink (i : β × _ × _).1 (ends (i : β × _ × _).1).1
      (ends (i : β × _ × _).1).2)
    (hQrat : (Q.coeffs : Set ℝ) ⊆ Set.range (algebraMap ℚ ℝ))
    (hQne : Q ≠ 0)
    (hQ : ∀ q : α × Fin (k + 2) → ℝ, MvPolynomial.eval q Q ≠ 0 →
      LinearIndependent ℝ
        (fun i : s => (PanelHingeFramework.ofNormals G ends q).toBodyHinge.panelRow ends i))
    {q : α × Fin (k + 2) → ℝ} (halg : AlgebraicIndependent ℚ q) :
    Module.finrank ℝ (PanelHingeFramework.ofNormals G ends q).toBodyHinge.infinitesimalMotions
      ≤ screwDim k * Nat.card α - Nat.card s := by
  classical
  haveI : Fintype α := Fintype.ofFinite α
  rw [Nat.card_eq_fintype_card]
  set F := (PanelHingeFramework.ofNormals G ends q).toBodyHinge with hF
  have hG : F.graph = G := rfl
  -- Footnote 6: the alg-indep seed is a non-root of the nonzero rational `Q`, so `hQ` gives the
  -- size-`#s` independent subfamily at `q` itself.
  have hq : MvPolynomial.eval q Q ≠ 0 :=
    MvPolynomial.eval_ne_zero_of_coeffs_subset_range_of_algebraicIndependent halg hQrat hQne
  have hLI : LinearIndependent ℝ (fun i : s => F.panelRow ends i) := hQ q hq
  haveI : Fintype s := Fintype.ofFinite s
  -- Each panel row of `s` lies in the rigidity rows; the per-index link witness is `hsupp`.
  have hsub : Submodule.span ℝ (Set.range (fun i : s => F.panelRow ends i))
      ≤ Submodule.span ℝ F.rigidityRows := by
    rw [Submodule.span_le]
    rintro _ ⟨⟨⟨e', t₁, t₂⟩, hi⟩, rfl⟩
    apply Submodule.subset_span
    refine ⟨e', (ends e').1, (ends e').2, by rw [hG]; exact hsupp _ hi,
      annihRow (F.supportExtensor e') t₁ t₂, ?_, rfl⟩
    rw [BodyHingeFramework.hingeRowBlock_apply, Submodule.mem_dualAnnihilator]
    intro x hx
    rw [Submodule.mem_span_singleton] at hx
    obtain ⟨r, rfl⟩ := hx
    rw [map_smul, annihRow_apply_self, smul_zero]
  have hrows : Nat.card s ≤ Module.finrank ℝ (Submodule.span ℝ F.rigidityRows) := by
    rw [Nat.card_eq_fintype_card, ← finrank_span_eq_card hLI]
    exact Submodule.finrank_mono hsub
  -- Rank-nullity: `dim Z + finrank (span rigidityRows) = D|α|`, so `dim Z ≤ D|α| − #s`.
  have hcompl : Module.finrank ℝ F.infinitesimalMotions
      + Module.finrank ℝ (Submodule.span ℝ F.rigidityRows)
      = screwDim k * Fintype.card α := by
    rw [F.infinitesimalMotions_eq_dualCoannihilator, Subspace.finrank_dualCoannihilator_eq,
      add_comm, Subspace.finrank_add_finrank_dualAnnihilator_eq, Subspace.dual_finrank_eq,
      BodyHingeFramework.finrank_screwAssignment]
  omega

/-- **Eq. (6.22) rank attainment at the inductively-fixed seed** (`lem:case-III-rank-attainment`,
the assembly of KT Claim~6.11's analytic kernel; Katoh–Tanigawa 2011 §6.4.1, footnote 6, eq.
(6.22), Phase 22d). The nested-induction step of Claim~6.11: the nested subgraph `G_v` — minimal
`k'`-dof with `k' = def(G̃_v)` (`lem:case-III-gap3-minimalKDof`) — attains its predicted rank
`D(|V_v|−1) − k'` at the same inductively-fixed (algebraically-independent) seed `q`, equivalently
`F.RankHypothesis (def G̃_v)`, i.e. `dim Z(G_v, q) = D + def`.

This is the `def > 0` packaging that pairs the two analytic halves into the exact rank:

* the **upper bound** `dim Z(G_v, q) ≤ D + def` — read off the eq. (6.22) upper bound
  `finrank_infinitesimalMotions_le_of_rankPolynomial_algebraicIndependent` (`dim Z ≤ D|α| − #s`) by
  feeding it the matroid-predicted full independent family: at the spanning seed `V(G) = univ`
  (`hspan`), a witnessed independent `panelRow`-subfamily `s` of size `#s ≥ D(|V|−1) − def`
  (`hcard`, the matroid rank `rank M(G̃) = D(|V|−1) − def` of `thm:def-eq-corank`) forces
  `dim Z ≤ D|α| − #s ≤ D + def`;
* the **lower bound** `D + def ≤ dim Z` — the genericity-free codimension brick `hub` of
  `rigidityMatrix_prop11`, now **discharged** there in-proof from the Phase-19 partition machinery
  (`screwDim_add_deficiency_le_finrank_infinitesimalMotions`), so this lemma supplies only the
  dimension fixing `n = k + 1` (`hn`) and the genuine-hinge condition `C(e) ≠ 0` (`hC`) the
  partition cut needs.

`rigidityMatrix_prop11` pins the equality from the two. The independent family `s` comes from
`G_v`'s minimal-`k'`-dof IH realization run through the device producer, supplying the rational
rank polynomial `Q` (`hQrat`/`hQne`/`hQ`) whose non-roots witness `s` (its edges linking in `G`,
`hsupp`); the alg-independence of the fixed seed `q` (`halg`) makes `q` a non-root *at the fixed
seed itself* (footnote 6). It is honest per the producer-scrutiny gate: the witnessed-rank input
`Q` is an unrelated rigid seed's rank certificate, not the rank concluded; the lower bound `hub` is
no longer assumed but derived from `hn`/`hC`. -/
theorem PanelHingeFramework.rankHypothesis_ofNormals_of_rankPolynomial_algebraicIndependent
    [Nonempty α] [Finite α] [Finite β] (G : Graph α β) (ends : β → α × α) (n : ℕ)
    (hspan : V(G) = Set.univ)
    {s : Set (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k)}
    {Q : MvPolynomial (α × Fin (k + 2)) ℝ}
    (hsupp : ∀ i ∈ s, G.IsLink (i : β × _ × _).1 (ends (i : β × _ × _).1).1
      (ends (i : β × _ × _).1).2)
    (hQrat : (Q.coeffs : Set ℝ) ⊆ Set.range (algebraMap ℚ ℝ))
    (hQne : Q ≠ 0)
    (hQ : ∀ q : α × Fin (k + 2) → ℝ, MvPolynomial.eval q Q ≠ 0 →
      LinearIndependent ℝ
        (fun i : s => (PanelHingeFramework.ofNormals G ends q).toBodyHinge.panelRow ends i))
    (hcard : (screwDim k * (V(G).ncard - 1) : ℤ) - G.deficiency n ≤ Nat.card s)
    {q : α × Fin (k + 2) → ℝ} (halg : AlgebraicIndependent ℚ q)
    (hn : n = k + 1)
    (hC : ∀ e, (PanelHingeFramework.ofNormals G ends q).toBodyHinge.supportExtensor e ≠ 0) :
    (PanelHingeFramework.ofNormals G ends q).toBodyHinge.RankHypothesis (G.deficiency n) := by
  classical
  haveI : Fintype α := Fintype.ofFinite α
  set F := (PanelHingeFramework.ofNormals G ends q).toBodyHinge with hF
  have hG : F.graph = G := rfl
  -- The eq. (6.22) upper bound at the fixed alg-indep seed: `dim Z ≤ D|α| − #s`.
  have hupper :=
    PanelHingeFramework.finrank_infinitesimalMotions_le_of_rankPolynomial_algebraicIndependent
      G ends hsupp hQrat hQne hQ halg
  rw [← hF] at hupper
  -- `V(G) = univ`, so `V(G).ncard = |α|` and the matroid-predicted count turns `dim Z ≤ D|α| − #s`
  -- into the `hgen` upper bound `dim Z ≤ D + def`.
  have hvcard : V(G).ncard = Nat.card α := by
    rw [hspan, Set.ncard_univ]
  have h1 : 1 ≤ Nat.card α := by
    rw [Nat.card_eq_fintype_card]; exact Fintype.card_pos
  rw [hvcard, ← Nat.cast_mul] at hcard
  -- The bridging product identity `D·|V| = D·(|V| − 1) + D` (needs `|V| ≥ 1`); with `hcard`'s
  -- `D·(|V|−1) − def ≤ #s` it turns `dim Z ≤ D·|V| − #s` into `dim Z ≤ D + def`. After rewriting
  -- the bridge into `hupper`, `generalize` the shared product `D·(|V|−1)` to a single fresh atom
  -- `Q'` so `omega` reasons linearly (the deficiency nonnegativity `hdef` rules out truncation).
  have hbridge : screwDim k * Nat.card α = screwDim k * (Nat.card α - 1) + screwDim k := by
    conv_lhs => rw [show Nat.card α = (Nat.card α - 1) + 1 from (Nat.sub_add_cancel h1).symm]
    rw [Nat.mul_add, Nat.mul_one]
  -- The deficiency is nonnegative (`V(G) = univ ≠ ∅`), ruling out the truncated branch of `hupper`.
  have hdef : 0 ≤ G.deficiency n :=
    G.deficiency_nonneg n (by rw [hspan]; exact Set.univ_nonempty)
  have hgen : (Module.finrank ℝ F.infinitesimalMotions : ℤ) ≤ screwDim k + G.deficiency n := by
    rw [hbridge] at hupper
    generalize screwDim k * (Nat.card α - 1) = Q' at hcard hupper
    clear hbridge
    omega
  -- `rigidityMatrix_prop11` pins the equality from `hub` (lower, now discharged in-proof from the
  -- partition machinery via `hn`/`hC`) and `hgen` (upper).
  exact rigidityMatrix_prop11 F n hn hC hgen

/-- **Case III (= Case II at `k = 0`), stratum 1: the eq. (6.12) `+(D−1)` block-triangular
placement** (`lem:case-II-realization-placement`, the first chunk of KT Lemma 6.10; Katoh–Tanigawa
2011 §6.4.1, eqs. (6.12), (6.16), Phase 22c). The first of three difficulty strata of the
conjecture's crux (the `theorem_55.hsplit` producer at `k = 0`): the *degenerate* 1-extension
placement of the reducible degree-2 body `v` that re-inserts `v` into the split-off `Gᵥ = G_v^{ab}`
and produces a linearly independent panel-row family of size `D(|V(G)|−1) − 1` — one row short
of the `k = 0` full target `D(|V(G)|−1)`, the missing row being the Case-III content (strata 2–3,
a later sub-phase). It is a **lower-bound brick** toward the (still red) `lem:case-II-realization`
/ `lem:case-III`, *not* a `HasFullRankRealization`.

Construction (KT eq. (6.12)). Take the inductive realization of `Gᵥ` at a seed `q` (rigid on
`V(Gᵥ)`, transversal hinges) and **place `v`'s panel normal at `n_a + t·n_b`** (`n_a = q(a,·)`,
`n_b = q(b,·)`, `t ≠ 0`): the shear identity `panelSupportExtensor_add_smul_right` makes `v`'s
`b`-hinge `e_b = vb` reproduce the `e₀ = ab`-hinge of the inductive realization (the `vb`-row
reproduces the `e₀`-row), while `panelSupportExtensor_add_smul_left` keeps `v`'s `a`-hinge a
nondegenerate line `L ⊂ Π(a)` (the `t ≠ 0` candidate, KT's actual eq. (6.12) — not the degenerate
`t = 0` placement `v = a`). The shared seed is `q₀ := fun p ↦ if p.1 = v then (n_a + t·n_b) p.2 else
q p`; overriding only the fresh body `v` leaves the `Gᵥ`-block untouched (`v ∉ V(Gᵥ)`, so no
`Gᵥ`-edge touches `v`: `ofNormals_update_eq_withNormal` +
`toBodyHinge_withNormal_infinitesimalMotions_eq`), so the IH rigidity transports to `q₀`.

Assembly (KT eq. (6.16), block-triangular). The `+(D−1)` *new* block is the `D − 1` panel rows of
`v`'s `b`-edge `e_b` (`exists_independent_panelRow_subfamily_of_edge`, N7b-1), independent through
`v`'s screw column (`linearIndependent_panelRow_comp_single_of_edge`, the `hnewpin` input). The
`D(|V(Gᵥ)|−1)` *old* block is the rigid `Gᵥ`-realization's linking panel rows
(`exists_independent_panelRow_subfamily_of_rigidOn_linking`, N7b-0), carried onto `G` along the
`e₀`-dropping injection (`exists_independent_panelRow_transport`, N7b-2, with `hrow := rfl` since
`panelRow` reads only `ends`/`q₀`, not the graph). The pin-a-body column split
(`linearIndependent_sum_pinned_block`, N7b-3) joins them: the old rows vanish at `update 0 v x`
(their edges avoid `v`), the new rows read `v`'s column. The count is
`(D−1) + D(|V(Gᵥ)|−1) = D(|V(G)|−1) − 1` (using `|V(Gᵥ)| = |V(G)| − 1`). All members are rigidity
rows of `ofNormals G ends q₀`, the input the device-row closure
`isInfinitesimallyRigidOn_vertexSet_of_independent_rigidityRows` (N7a form (b)) consumes — but here
the family is one short of `D(|V(G)|−1)`, so it certifies only `rank R(G,p₁) ≥ D(|V(G)|−1) − 1`. -/
theorem PanelHingeFramework.case_II_placement_eq612 [DecidableEq α] [Finite α] [Finite β]
    (G Gv : Graph α β) (hGv : Gv ≤ G) (ends : β → α × α)
    -- the split-off block and the re-inserted body `v`, with its two new hinges `e_a = va`,
    -- `e_b = vb`. `e_a`'s `G`-link is crux-strata input, so stratum 1 needs only its selector.
    {v a b : α} {e_a e_b : β} (hvVc : v ∉ V(Gv)) (haVc : a ∈ V(Gv)) (hbVc : b ∈ V(Gv))
    (hG_eb : G.IsLink e_b v b) (hends_eb : ends e_b = (v, b))
    (_hG_ea : G.IsLink e_a v a) (hends_ea : ends e_a = (v, a))
    -- `|V(Gᵥ)| = |V(G)| − 1` (carried from `vertexSet_splitOff` downstream)
    (hVcard : V(Gv).ncard = V(G).ncard - 1)
    -- the inductive realization of `Gᵥ` at a seed `q`: rigid on `V(Gᵥ)`, transversal hinges, links
    {q : α × Fin (k + 2) → ℝ}
    (hends_Gv : ∀ e u w, Gv.IsLink e u w → Gv.IsLink e (ends e).1 (ends e).2)
    (hne_Gv : ∀ e, Gv.IsLink e (ends e).1 (ends e).2 →
      (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge.supportExtensor e ≠ 0)
    (hrig : (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge.IsInfinitesimallyRigidOn V(Gv))
    -- the shear parameter `t ≠ 0` and the eq. (6.12) shared seed `q₀`
    {t : ℝ} (ht : t ≠ 0)
    (q₀ : α × Fin (k + 2) → ℝ)
    (hq₀ : q₀ = fun p => if p.1 = v then
        ((fun i => q (a, i)) + t • (fun i => q (b, i))) p.2 else q p)
    -- the inductive realization's `e₀ = ab`-hinge is transversal (so the reproduced `vb`-row ≠ 0)
    (hgab : LinearIndependent ℝ ![(fun i => q (a, i)), (fun i => q (b, i))]) :
    -- a `D(|V(G)|−1) − 1`-size independent panel-row family of `ofNormals G ends q₀`, all rigidity
    -- rows — the eq. (6.12) `+(D−1)` lower bound `rank R(G,p₁) ≥ D(|V(G)|−1) − 1` — together with
    -- `v`'s `a`-hinge nondegeneracy (the `va`-line `L ⊂ Π(a)`, KT's eq. (6.12) candidate, `t ≠ 0`).
    (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.supportExtensor e_a ≠ 0 ∧
    ∃ s : Set (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k),
      screwDim k * (V(G).ncard - 1) - 1 ≤ Nat.card s ∧
      (∀ i ∈ s, (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.panelRow ends i
        ∈ (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.rigidityRows) ∧
      LinearIndependent ℝ (fun i : s =>
        (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.panelRow ends i) := by
  classical
  haveI : Fintype α := Fintype.ofFinite α
  set FG := (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge with hFG
  set n_a : Fin (k + 2) → ℝ := fun i => q (a, i) with hn_a
  set n_b : Fin (k + 2) → ℝ := fun i => q (b, i) with hn_b
  -- (1) The shared seed is the IH seed with `v`'s normal overridden by `n_a + t • n_b`, so the IH
  -- rigidity transports to `q₀` (overriding the fresh `v ∉ V(Gᵥ)` leaves the `Gᵥ`-block untouched).
  have hqeq : (fun p => if p.1 = v then ((n_a + t • n_b) : Fin (k + 2) → ℝ) p.2 else q p) = q₀ := by
    rw [hq₀]
  have hwN : PanelHingeFramework.ofNormals Gv ends q₀
      = (PanelHingeFramework.ofNormals Gv ends q).withNormal v (n_a + t • n_b) := by
    rw [← hqeq]
    exact PanelHingeFramework.ofNormals_update_eq_withNormal Gv ends q v (n_a + t • n_b)
  -- No `Gᵥ`-edge touches `v` (its endpoints lie in `V(Gᵥ)`, and `v ∉ V(Gᵥ)`).
  have hvedge : ∀ e u w, Gv.IsLink e u w → (ends e).1 ≠ v ∧ (ends e).2 ≠ v := by
    intro e u w he
    have hl := hends_Gv e u w he
    exact ⟨fun h => hvVc (h ▸ hl.left_mem), fun h => hvVc (h ▸ hl.right_mem)⟩
  -- The motion space is unchanged when overriding the unhinged `v`, so the IH rigidity transports.
  have hZeq : (PanelHingeFramework.ofNormals Gv ends q₀).toBodyHinge.infinitesimalMotions
      = (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge.infinitesimalMotions := by
    rw [hwN]
    exact (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge_withNormal_infinitesimalMotions_eq
      v (n_a + t • n_b) hvedge
  have hrig₀ :
      (PanelHingeFramework.ofNormals Gv ends q₀).toBodyHinge.IsInfinitesimallyRigidOn V(Gv) := by
    intro S hS u hu w hw
    refine hrig S ?_ u hu w hw
    rw [← BodyHingeFramework.mem_infinitesimalMotions, ← hZeq,
      BodyHingeFramework.mem_infinitesimalMotions] at *
    exact hS
  -- The `Gᵥ`-hinges stay transversal at `q₀` (endpoints avoid `v`, where `q₀` agrees with `q`).
  have hne₀ : ∀ e, Gv.IsLink e (ends e).1 (ends e).2 →
      (PanelHingeFramework.ofNormals Gv ends q₀).toBodyHinge.supportExtensor e ≠ 0 := by
    intro e he
    obtain ⟨h₁, h₂⟩ := hvedge e _ _ he
    rw [hwN, (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge_withNormal_supportExtensor_of_ne
      v (n_a + t • n_b) e (by simpa using h₁) (by simpa using h₂)]
    exact hne_Gv e he
  -- (2) OLD block (N7b-0, `_linking`): the rigid `Gᵥ`-realization carries `D(|V(Gᵥ)|−1)`
  -- independent linking panel rows of `ofNormals Gv ends q₀`.
  have hVGvne : V(Gv).Nonempty := ⟨b, hbVc⟩
  set FGv := (PanelHingeFramework.ofNormals Gv ends q₀).toBodyHinge with hFGv
  obtain ⟨so, hso_link, hso_card, hso_indep⟩ :=
    FGv.exists_independent_panelRow_subfamily_of_rigidOn_linking (ends := ends)
      (by simpa [hFGv] using hends_Gv) (by simpa [hFGv] using hne₀) (by simpa [hFGv] using hVGvne)
      (by simpa [hFGv] using hrig₀)
  -- (3) Transport the old block onto `G` (N7b-2; `panelRow` reads only `ends`/`q₀`, not the graph,
  -- so `hrow := rfl`).
  have hso_indep_G : LinearIndependent ℝ (fun i : so =>
      FG.panelRow ends (i : β × _ × _)) :=
    PanelHingeFramework.exists_independent_panelRow_transport Gv G ends ends q₀ q₀
      (f := id) Function.injective_id (fun i => rfl) hso_indep
  -- The re-inserted body `v` and its neighbour `b` are distinct (`b ∈ V(Gᵥ)`, `v ∉ V(Gᵥ)`).
  have hvb : v ≠ b := fun h => hvVc (h ▸ hbVc)
  -- The shared seed reads `q₀(v,·) = n_a + t·n_b` and `q₀(b,·) = n_b`.
  have hq₀v : (fun i => q₀ (v, i)) = n_a + t • n_b := by
    funext i; rw [hq₀]; simp
  have hq₀b : (fun i => q₀ (b, i)) = n_b := by
    funext i; rw [hq₀, hn_b]; simp only [if_neg hvb.symm]
  have hva : v ≠ a := fun h => hvVc (h ▸ haVc)
  have hq₀a : (fun i => q₀ (a, i)) = n_a := by
    funext i; rw [hq₀, hn_a]; simp only [if_neg hva.symm]
  -- The `va`-hinge `e_a` stays a nondegenerate line `L ⊂ Π(a)` (KT eq. (6.12), `t ≠ 0`).
  have hane : FG.supportExtensor e_a ≠ 0 := by
    rw [PanelHingeFramework.toBodyHinge_supportExtensor, PanelHingeFramework.ofNormals_ends,
      PanelHingeFramework.ofNormals_normal, PanelHingeFramework.ofNormals_normal, hends_ea]
    simp only [hq₀v, hq₀a, panelSupportExtensor_add_smul_left]
    exact smul_ne_zero (neg_ne_zero.mpr ht) ((panelSupportExtensor_ne_zero_iff n_a n_b).mpr hgab)
  -- (4) NEW block (N7b-1): the reproduced `vb`-hinge `e_b` is transversal
  -- (`panelSupportExtensor_add_smul_right` reproduces the transversal `e₀ = ab`-hinge), giving
  -- `D − 1` independent new rows.
  have hnewne : FG.supportExtensor e_b ≠ 0 := by
    rw [PanelHingeFramework.toBodyHinge_supportExtensor, PanelHingeFramework.ofNormals_ends,
      PanelHingeFramework.ofNormals_normal, PanelHingeFramework.ofNormals_normal, hends_eb]
    simp only [hq₀v, hq₀b, panelSupportExtensor_add_smul_right]
    exact (panelSupportExtensor_ne_zero_iff n_a n_b).mpr hgab
  have hev : (ends e_b).2 ≠ (ends e_b).1 := by rw [hends_eb]; exact hvb.symm
  obtain ⟨sn, hsn_e, hsn_card, hsn_indep⟩ :=
    FG.exists_independent_panelRow_subfamily_of_edge
      (ends := ends) (e := e_b) (by rw [hends_eb]; exact hvb) hnewne
  -- `hnewpin`: the new rows stay independent through `v = (ends e_b).1`'s screw column.
  have hnewpin := FG.linearIndependent_panelRow_comp_single_of_edge
    (ends := ends) (e := e_b) hev hsn_e hsn_indep
  -- (5) The old rows vanish at `update 0 v x` (their `Gᵥ`-edges avoid `v`).
  have hold : ∀ (j : so) (x : ScrewSpace k),
      FG.panelRow ends (j : β × _ × _)
        (Function.update (0 : α → ScrewSpace k) v x) = 0 := by
    rintro ⟨i, hi⟩ x
    have hlink := hso_link _ hi
    have h₁ : (ends i.1).1 ≠ v := fun h => hvVc (h ▸ hlink.left_mem)
    have h₂ : (ends i.1).2 ≠ v := fun h => hvVc (h ▸ hlink.right_mem)
    rw [BodyHingeFramework.panelRow, BodyHingeFramework.hingeRow_apply,
      Function.update_of_ne h₁, Function.update_of_ne h₂, Pi.zero_apply, Pi.zero_apply, sub_zero,
      map_zero]
  -- (6) The two blocks are jointly independent (N7b-3, the pin-a-body split = KT eq. (6.16)).
  have hunion : LinearIndependent ℝ (Sum.elim
      (fun i : sn => FG.panelRow ends
        (i : β × _ × _))
      (fun i : so => FG.panelRow ends
        (i : β × _ × _))) := by
    have hpin : LinearIndependent ℝ (fun i : sn =>
        (FG.panelRow ends (i : β × _ × _)).comp
          (LinearMap.single ℝ (fun _ : α => ScrewSpace k) v)) := by
      have := hnewpin
      rw [hends_eb] at this
      exact this
    exact BodyHingeFramework.linearIndependent_sum_pinned_block (v := v) hold hpin hso_indep_G
  -- (7) Package the `Sum.elim` family as a single `Set`-indexed panel-row subfamily. The map
  -- sending each block index to its underlying `(edge, ⋀^k-pair)` is injective: `sn`-indices use
  -- the new edge `e_b ∉ E(Gᵥ)`, `so`-indices use `Gᵥ`-edges, so the two are disjoint.
  -- No `so`-index uses the new edge `e_b`: else `e_b` would be a `Gᵥ`-edge with endpoint `v`.
  have hso_ne_eb : ∀ i ∈ so, (i : β × _ × _).1 ≠ e_b := by
    intro i hi heq
    have hl := hso_link i hi
    rw [heq, hends_eb] at hl
    exact hvVc hl.left_mem
  set j : (sn ⊕ so) → (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k) :=
    Sum.elim (fun i => (i : β × _ × _)) (fun i => (i : β × _ × _)) with hj
  have hjinj : Function.Injective j := by
    rintro (⟨in₁, hin₁⟩ | ⟨io₁, hio₁⟩) (⟨in₂, hin₂⟩ | ⟨io₂, hio₂⟩) hab <;>
      simp only [hj, Sum.elim_inl, Sum.elim_inr] at hab
    · exact congrArg Sum.inl (Subtype.ext hab)
    · have : (io₂ : β × _ × _).1 = e_b := by rw [← congrArg Prod.fst hab]; exact hsn_e _ hin₁
      exact absurd this (hso_ne_eb _ hio₂)
    · have : (io₁ : β × _ × _).1 = e_b := by rw [congrArg Prod.fst hab]; exact hsn_e _ hin₂
      exact absurd this (hso_ne_eb _ hio₁)
    · exact congrArg Sum.inr (Subtype.ext hab)
  -- `s := range j`, the union index set; the panel-row family on it is the `Sum.elim` family
  -- reindexed across `Equiv.ofInjective j`, hence independent and a rigidity-row family.
  refine ⟨hane, Set.range j, ?_, ?_, ?_⟩
  · -- Count: `(D−1) + D(|V(Gᵥ)|−1) = D(|V(G)|−1) − 1` (using `|V(Gᵥ)| = |V(G)| − 1`).
    rw [Nat.card_range_of_injective hjinj, Nat.card_sum, hsn_card]
    have hgraph : V((PanelHingeFramework.ofNormals Gv ends q₀).toBodyHinge.graph) = V(Gv) := rfl
    rw [hgraph] at hso_card
    rw [hso_card, hVcard]
    have h1 : 1 ≤ V(G).ncard := (Set.ncard_pos (Set.toFinite _)).2 ⟨v, hG_eb.left_mem⟩
    -- `D(m−1)−1 ≤ (D−1) + D(m−1−1)`; with `D(m−1) = D(m−2) + D` (for `m ≥ 1`) this is an equality.
    obtain ⟨m, hm⟩ : ∃ m, V(G).ncard = m + 1 := ⟨V(G).ncard - 1, by omega⟩
    rw [hm]
    simp only [Nat.add_sub_cancel]
    cases m with
    | zero => simp
    | succ m' =>
      rw [Nat.add_sub_cancel, Nat.mul_succ]
      omega
  · -- Membership: each row's edge links in `G` (new edge `e_b`, or a `Gᵥ`-edge ≤ `G`).
    rintro i ⟨(⟨ic, hic⟩ | ⟨ic, hic⟩), rfl⟩ <;>
      refine FG.panelRow_mem_rigidityRows ?_
    · change G.IsLink _ _ _
      simp only [hj, Sum.elim_inl]; rw [hsn_e _ hic, hends_eb]; exact hG_eb
    · change G.IsLink _ _ _
      simp only [hj, Sum.elim_inr]
      exact (Graph.IsSubgraph.isLink_iff hGv (hso_link _ hic).edge_mem).mp (hso_link _ hic)
  · -- Independence: reindex the `Sum.elim` family across `Equiv.ofInjective j`.
    have hreindex : (fun i : Set.range j =>
        FG.panelRow ends (i : β × _ × _))
        ∘ (Equiv.ofInjective j hjinj)
      = Sum.elim
        (fun i : sn => FG.panelRow ends
          (i : β × _ × _))
        (fun i : so => FG.panelRow ends
          (i : β × _ × _)) := by
      funext a
      simp only [Function.comp_apply, Equiv.ofInjective_apply, hj]
      cases a <;> rfl
    set ej := Equiv.ofInjective j hjinj with hej
    have h := hunion.comp ej.symm ej.symm.injective
    rw [← hreindex, Function.comp_assoc, Equiv.self_comp_symm, Function.comp_id] at h
    exact h

/-- **The Claim~6.11 redundant `ab`-row: a small corank over the `ab`-block forces one of its
`D − 1` rows redundant** (`lem:case-III-claim-6-11-redundant-row`, the linear-algebra core of KT
Claim~6.11's eq. (6.23); Katoh–Tanigawa 2011 §6.4.1, eq. (6.23), Phase 22d). The geometric
instantiation of the abstract finrank pigeonhole
(`Submodule.exists_mem_sup_span_image_compl_of_finrank_lt`) at the `D − 1` panel rows of a single
transversal hinge `e` (= the `ab`-edge of KT's split-off graph `G_v^{ab}`).

Set `W := span(R(G_v)-rows)` for the smaller graph `G_v = G_v^{ab} − ab` (carried here abstractly
as any subspace). The `e`-block is the per-edge panel-row span `span {panelRow ends (e, ·, ·)}` — a
`(D − 1)`-dimensional space (`span_panelRow_edge_eq` + `finrank_hingeRowBlock`), spanned by a `Fin
(D − 1)`-indexed independent family `r` (`exists_independent_panelRow_of_edge`). KT's two rank
inputs — eq. (6.18) `finrank (W ⊔ e-block) = D(|V_v|−1)` and eq. (6.22)
`finrank W = D(|V_v|−1) − k'` with `k' ≤ D − 2` — say exactly that the `e`-block raises
`finrank W` by `k' < D − 1`, i.e.
`finrank (W ⊔ span (range r)) < finrank W + (D − 1)` (the hypothesis `hgap`). The pigeonhole then
yields an index `i₀` whose row `r i₀` is *redundant modulo `W` and the other `e`-rows*:
`r i₀ ∈ W ⊔ span (r '' {j ≠ i₀})` — KT's eq. (6.23), one of the `ab`-rows is a row-combination of
the rest plus the `R(G_v)` rows, so dropping it does not lower the rank.

The produced family `r` is independent and lands in the per-edge panel-row span; its span *is* that
block (an `≤` upgraded to `=` by equal finrank `D − 1`), so a caller pairing this with the
eq. (6.18)/(6.22) bridge identities feeds `hgap` from `W = span(R(G_v)-rows)`. This is the pure-LA
step ③ of the Gap-1 chain (`notes/Phase22d.md`); the geometric content beyond the abstract leaf is
that the `e`-block has dimension exactly `D − 1` and is spanned by the independent family `r`. -/
theorem BodyHingeFramework.exists_redundant_panelRow_of_edge_of_finrank_lt
    [Finite α] (F : BodyHingeFramework k α β) {ends : β → α × α} {e : β}
    (huv : (ends e).1 ≠ (ends e).2) (he : F.supportExtensor e ≠ 0)
    (W : Submodule ℝ (Module.Dual ℝ (α → ScrewSpace k)))
    (hgap : Module.finrank ℝ (W ⊔ Submodule.span ℝ (Set.range (fun p :
        Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k =>
          F.panelRow ends (e, p.1, p.2))) : Submodule ℝ (Module.Dual ℝ (α → ScrewSpace k)))
      < Module.finrank ℝ W + (screwDim k - 1)) :
    ∃ (r : Fin (screwDim k - 1) → Module.Dual ℝ (α → ScrewSpace k)),
      LinearIndependent ℝ r ∧
      Submodule.span ℝ (Set.range r) = Submodule.span ℝ (Set.range (fun p :
        Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k =>
          F.panelRow ends (e, p.1, p.2))) ∧
      ∃ i, r i ∈ W ⊔ Submodule.span ℝ (r '' {j | j ≠ i}) := by
  haveI : Fintype α := Fintype.ofFinite α
  haveI : FiniteDimensional ℝ (ScrewSpace k) := inferInstance
  set Eblk := Submodule.span ℝ (Set.range (fun p : Set.powersetCard (Fin (k + 2)) k
    × Set.powersetCard (Fin (k + 2)) k => F.panelRow ends (e, p.1, p.2))) with hEblk
  -- The `D − 1` independent panel rows of the transversal hinge `e` (N7b-1, `Fin`-indexed form).
  obtain ⟨r, hr, hmem⟩ := F.exists_independent_panelRow_of_edge huv he
  -- They span the `e`-block: `≤` by membership, `=` by equal finrank `D − 1`.
  have hrspan : Submodule.span ℝ (Set.range r) = Eblk := by
    refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
    · rw [Submodule.span_le]; rintro _ ⟨i, rfl⟩; rw [hEblk]; exact hmem i
    · rw [finrank_span_eq_card hr, Fintype.card_fin, hEblk, F.finrank_span_panelRow_edge huv he]
  refine ⟨r, hr, hrspan, ?_⟩
  -- `Fintype.card (Fin (D − 1)) = D − 1`, and `span (range r) = e-block`, so `hgap` is exactly the
  -- abstract pigeonhole's finrank hypothesis at the family `r`.
  apply Submodule.exists_mem_sup_span_image_compl_of_finrank_lt W r
  rw [Fintype.card_fin, hrspan]
  exact hgap

/-- **Claim 6.11, eq. (6.23): the deleted `ab`-edge has a redundant row**
(`lem:case-III-claim-6-11`,
the Gap-1 corank-gap discharge; Katoh–Tanigawa 2011 §6.4.1, eq. (6.23), Phase 22d). The geometric
*instantiation* of the abstract redundant-row pigeonhole
(`exists_redundant_panelRow_of_edge_of_finrank_lt`) at KT's two specific graphs: the split-off
`Gab = G_v^{ab}` (`0`-dof) and its single-edge deletion `Gv = G_v^{ab} − ab` (minimal `k'`-dof,
`k' ≤ D − 2`). Both frameworks are `ofNormals · ends q` at the *same* inductively-fixed seed `q` and
selector `ends`, so they agree on every supporting extensor (`panelRow`/`supportExtensor` read only
`ends`/`q`, not the graph), and their link sets differ by exactly the `ab`-edge `e₀` linking `a`,
`b` (`he₀`, with `Gv`'s links a subset of `Gab`'s, `hle`, and every `Gab`-link a `Gv`-link or `e₀`,
`hsplit`).

KT's two rank inputs are the two `finrank` equations: eq. (6.18)
`finrank (span R(Gab,q)-rows) = D(m−1)` (`h618`, the `0`-dof full rank, `m = |V(Gab)| = |V(Gv)|`,
from the seed-rank bridge `lem:case-III-seed-rank-bridge` at the rigid `Gab`) and eq. (6.22)
`finrank (span R(Gv,q)-rows) = D(m−1) − k'` with `k' ≤ D − 2` (`h622`/`hk'`, from the
rank-attainment packaging `lem:case-III-rank-attainment` + Gap-3 `lem:case-III-gap3-minimalKDof`).
The row-set identity `span R(Gab)-rows = W ⊔ ab-block`
(`span_rigidityRows_eq_sup_span_panelRow_edge`,
`W = span R(Gv)-rows`) turns eq. (6.18) into `finrank (W ⊔ ab-block) = D(m−1)`, so the `ab`-block
raises `finrank W = D(m−1) − k'` by only `k' < D − 1` — exactly the corank gap `hgap` the
pigeonhole needs. The conclusion is KT's eq. (6.23): the `D − 1` independent `ab`-rows have one
member redundant
modulo `W` and the rest, so dropping it does not lower the rank — the `+1` that (in the deferred
candidate-completion assembly) lifts the stratum-1 brick `D(|V|−1) − 1` to full `D(|V|−1)`. -/
theorem BodyHingeFramework.exists_redundant_panelRow_ab_of_finrank_eq
    [Finite α] {Gab Gv : Graph α β} {ends : β → α × α} {q : α × Fin (k + 2) → ℝ} {e₀ : β}
    (hD : 2 ≤ screwDim k)
    (huv : (ends e₀).1 ≠ (ends e₀).2)
    (hne₀ : (PanelHingeFramework.ofNormals Gab ends q).toBodyHinge.supportExtensor e₀ ≠ 0)
    (he₀ : Gab.IsLink e₀ (ends e₀).1 (ends e₀).2)
    (hle : ∀ e u v, Gv.IsLink e u v → Gab.IsLink e u v)
    (hsplit : ∀ e u v, Gab.IsLink e u v → Gv.IsLink e u v ∨ e = e₀)
    {m k' : ℕ} (hk' : k' ≤ screwDim k - 2)
    (h618 : Module.finrank ℝ (Submodule.span ℝ
        (PanelHingeFramework.ofNormals Gab ends q).toBodyHinge.rigidityRows)
      = screwDim k * (m - 1))
    (h622 : Module.finrank ℝ (Submodule.span ℝ
        (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge.rigidityRows)
      = screwDim k * (m - 1) - k') :
    ∃ (r : Fin (screwDim k - 1) → Module.Dual ℝ (α → ScrewSpace k)),
      LinearIndependent ℝ r ∧
      Submodule.span ℝ (Set.range r) = Submodule.span ℝ (Set.range (fun p :
        Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k =>
          (PanelHingeFramework.ofNormals Gab ends q).toBodyHinge.panelRow ends (e₀, p.1, p.2))) ∧
      ∃ i, r i ∈ Submodule.span ℝ
          (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge.rigidityRows
        ⊔ Submodule.span ℝ (r '' {j | j ≠ i}) := by
  haveI : FiniteDimensional ℝ (ScrewSpace k) := inferInstance
  set Fab := (PanelHingeFramework.ofNormals Gab ends q).toBodyHinge with hFab
  set Fv := (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge with hFv
  set W := Submodule.span ℝ Fv.rigidityRows with hW
  set Eblk := Submodule.span ℝ (Set.range (fun p : Set.powersetCard (Fin (k + 2)) k
    × Set.powersetCard (Fin (k + 2)) k => Fab.panelRow ends (e₀, p.1, p.2))) with hEblk
  -- The two frameworks agree on every supporting extensor (graph-independent), so the row-set
  -- identity `span R(Gab)-rows = W ⊔ ab-block` applies (the only difference is the `ab`-edge).
  have hext : ∀ e, Fab.supportExtensor e = Fv.supportExtensor e := fun e => rfl
  have hrow : Submodule.span ℝ Fab.rigidityRows = W ⊔ Eblk :=
    Fab.span_rigidityRows_eq_sup_span_panelRow_edge Fv hext hne₀ he₀ hle hsplit
  -- Eq. (6.18) `finrank (W ⊔ ab-block) = D(m−1)` and eq. (6.22) `finrank W = D(m−1) − k'`, with
  -- `k' ≤ D − 2`, give the corank gap: the `ab`-block raises `finrank W` by `k' < D − 1`.
  have hgap : Module.finrank ℝ (W ⊔ Eblk : Submodule ℝ (Module.Dual ℝ (α → ScrewSpace k)))
      < Module.finrank ℝ W + (screwDim k - 1) := by
    have hWle : Module.finrank ℝ W
        ≤ Module.finrank ℝ (W ⊔ Eblk : Submodule ℝ (Module.Dual ℝ (α → ScrewSpace k))) :=
      Submodule.finrank_mono le_sup_left
    rw [← hrow, h618] at hWle ⊢
    rw [hW, h622] at hWle ⊢
    omega
  exact Fab.exists_redundant_panelRow_of_edge_of_finrank_lt huv hne₀ W hgap

/-- **Claim 6.11, eqs. (6.24)–(6.25): the redundant `ab`-row as an explicit vanishing combination**
(`lem:case-III-candidate-row` infra, the candidate-completion's eq. (6.24)/(6.25) extraction;
Katoh–Tanigawa 2011 §6.4.1, eqs. (6.24)–(6.25), Phase 22e). The functional-identity form of KT
Claim 6.11 (eq. (6.23)) that the candidate-completion row operation (eqs. (6.26)–(6.28)) consumes.
Where `exists_redundant_panelRow_ab_of_finrank_eq` (eq. (6.23)) delivers the *membership*
`r i^* ∈ span(R(G_v, q)-rows) ⊔ span(r '' {j ≠ i^*})` — the `(D − 1)` independent `ab`-rows `r`
spanning the `ab`-block, one of them redundant modulo the `G_v`-rows and the rest — this lemma
unwinds that membership (`Submodule.mem_sup`) into KT's eq. (6.24): the redundant `ab`-row `r i^*`
*equals* a `G_v`-row element `wGv ∈ span(R(G_v, q)-rows)` plus an explicit combination
`wOther ∈ span(r '' {j ≠ i^*})` of the *other* `ab`-rows. Rearranged, this is the vanishing
combination
\[ r\,i^* \;-\; w_{\mathrm{Other}} \;-\; w_{\mathrm{Gv}} \;=\; 0, \]
i.e.\ eq. (6.24) `Σ_j λ_{(ab)j} R(G_v^{ab}, q; (ab)j) + Σ_{e, j} λ_{ej} R(G_v^{ab}, q; ej) = 0`
with the `(ab)i^*`-coefficient `λ_{(ab)i^*} = 1` (eq. (6.25)) — the `r i^*` term carries coefficient
`1`, `wOther` the other `ab`-coefficients `λ_{(ab)j}` (`j ≠ i^*`), and `wGv` the `E_v`-coefficients
`λ_{ej}`. This decomposition (`r i^*` = `G_v`-part + other-`ab`-part) is the precise input KT
transport from `R(G_v^{ab}, q)` up to `R(G, p_1)` across the seam (eqs. (6.26)–(6.27)) to build the
pure-`v`-column row `w` of eq. (6.28); the transport + the eq. (6.43) `a`-block-vanishing of the
combination remain the open crux of `lem:case-III-candidate-row`. -/
theorem BodyHingeFramework.exists_redundant_panelRow_ab_decomposition
    [Finite α] {Gab Gv : Graph α β} {ends : β → α × α} {q : α × Fin (k + 2) → ℝ} {e₀ : β}
    (hD : 2 ≤ screwDim k)
    (huv : (ends e₀).1 ≠ (ends e₀).2)
    (hne₀ : (PanelHingeFramework.ofNormals Gab ends q).toBodyHinge.supportExtensor e₀ ≠ 0)
    (he₀ : Gab.IsLink e₀ (ends e₀).1 (ends e₀).2)
    (hle : ∀ e u v, Gv.IsLink e u v → Gab.IsLink e u v)
    (hsplit : ∀ e u v, Gab.IsLink e u v → Gv.IsLink e u v ∨ e = e₀)
    {m k' : ℕ} (hk' : k' ≤ screwDim k - 2)
    (h618 : Module.finrank ℝ (Submodule.span ℝ
        (PanelHingeFramework.ofNormals Gab ends q).toBodyHinge.rigidityRows)
      = screwDim k * (m - 1))
    (h622 : Module.finrank ℝ (Submodule.span ℝ
        (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge.rigidityRows)
      = screwDim k * (m - 1) - k') :
    ∃ (r : Fin (screwDim k - 1) → Module.Dual ℝ (α → ScrewSpace k)),
      LinearIndependent ℝ r ∧
      Submodule.span ℝ (Set.range r) = Submodule.span ℝ (Set.range (fun p :
        Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k =>
          (PanelHingeFramework.ofNormals Gab ends q).toBodyHinge.panelRow ends (e₀, p.1, p.2))) ∧
      ∃ (i : Fin (screwDim k - 1))
        (wGv wOther : Module.Dual ℝ (α → ScrewSpace k)),
        wGv ∈ Submodule.span ℝ
          (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge.rigidityRows ∧
        wOther ∈ Submodule.span ℝ (r '' {j | j ≠ i}) ∧
        r i = wGv + wOther := by
  obtain ⟨r, hr, hrspan, i, hmem⟩ :=
    BodyHingeFramework.exists_redundant_panelRow_ab_of_finrank_eq hD huv hne₀ he₀ hle hsplit hk'
      h618 h622
  obtain ⟨wGv, hwGv, wOther, hwOther, hsum⟩ := Submodule.mem_sup.1 hmem
  exact ⟨r, hr, hrspan, i, wGv, wOther, hwGv, hwOther, hsum.symm⟩

/-- **Eqs. (6.24)/(6.25): the redundant-`ab`-row decomposition as an explicit unit-normalized
nonzero combination** (`lem:case-III-claim612-r-nonzero` infra, the candidate vector `r̂` of KT
eqs. (6.24)/(6.25); Katoh–Tanigawa 2011 §6.4.1, eqs. (6.24)–(6.25), Phase 22g). Where
`exists_redundant_panelRow_ab_decomposition` (eq. (6.24)) delivers the redundant `ab`-row as
`r i^* = wGv + wOther` — its `G_v`-row part `wGv` plus an expansion `wOther` of the *other*
`ab`-rows — this leaf reads off KT's eq. (6.25): the explicit coefficient family `λ_{(ab)j}` with
the redundant index's coefficient pinned to `λ_{(ab)i^*} = 1`, for which the candidate vector
`r̂ := ∑_j λ_{(ab)j} r_j` (KT eq. (6.27)) is the `G_v`-row part `wGv` of the redundant row and is
**nonzero** (it carries the unit coefficient on the independent member `i^*`).

The coefficient extraction is the graph-free linear-algebra leaf
`exists_smul_combination_eq_sub_of_mem_span_image_compl` applied to the decomposition's membership
`wOther ∈ span (r '' {j | j ≠ i})`: it expands `wOther` over `{r_j : j ≠ i^*}` and pins the `i^*`
coefficient to `1`, giving `∑_j λ_j r_j = r i^* − wOther = wGv` (the eq. (6.24) rearrangement) with
`λ_{i^*} = 1`, hence `r̂ ≠ 0`. The `r̂ ≠ 0` conclusion is the `hr` input the Claim-6.12 disjunction
(`case_III_claim612`, via `candidateRow_ne_zero`) needs; `r̂ = wGv` ties it to the `G_v`-row part
the candidate-completion row operation (`exists_candidate_row_eq612`) consumes. -/
theorem BodyHingeFramework.exists_redundant_panelRow_ab_lam
    [Finite α] {Gab Gv : Graph α β} {ends : β → α × α} {q : α × Fin (k + 2) → ℝ} {e₀ : β}
    (hD : 2 ≤ screwDim k)
    (huv : (ends e₀).1 ≠ (ends e₀).2)
    (hne₀ : (PanelHingeFramework.ofNormals Gab ends q).toBodyHinge.supportExtensor e₀ ≠ 0)
    (he₀ : Gab.IsLink e₀ (ends e₀).1 (ends e₀).2)
    (hle : ∀ e u v, Gv.IsLink e u v → Gab.IsLink e u v)
    (hsplit : ∀ e u v, Gab.IsLink e u v → Gv.IsLink e u v ∨ e = e₀)
    {m k' : ℕ} (hk' : k' ≤ screwDim k - 2)
    (h618 : Module.finrank ℝ (Submodule.span ℝ
        (PanelHingeFramework.ofNormals Gab ends q).toBodyHinge.rigidityRows)
      = screwDim k * (m - 1))
    (h622 : Module.finrank ℝ (Submodule.span ℝ
        (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge.rigidityRows)
      = screwDim k * (m - 1) - k') :
    ∃ (r : Fin (screwDim k - 1) → Module.Dual ℝ (α → ScrewSpace k)) (lam : Fin (screwDim k - 1) → ℝ)
      (i : Fin (screwDim k - 1)),
      LinearIndependent ℝ r ∧
      Submodule.span ℝ (Set.range r) = Submodule.span ℝ (Set.range (fun p :
        Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k =>
          (PanelHingeFramework.ofNormals Gab ends q).toBodyHinge.panelRow ends (e₀, p.1, p.2))) ∧
      lam i = 1 ∧
      (∑ j, lam j • r j) ∈ Submodule.span ℝ
        (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge.rigidityRows ∧
      (∑ j, lam j • r j) ≠ 0 := by
  obtain ⟨r, hr, hrspan, i, wGv, wOther, hwGv, hwOther, hsum⟩ :=
    BodyHingeFramework.exists_redundant_panelRow_ab_decomposition hD huv hne₀ he₀ hle hsplit hk'
      h618 h622
  -- `r i = wGv + wOther` with `wOther ∈ span (r '' {j ≠ i})`; extract the unit-normalized
  -- coefficients `λ` (KT eq. (6.25), `λ i^* = 1`) for which `∑ λ_j r_j = r i − wOther = wGv`.
  obtain ⟨lam, hlam_i, hlam_sum, hlam_ne⟩ :=
    exists_smul_combination_eq_sub_of_mem_span_image_compl hr hwOther
  -- `∑ λ_j r_j = r i − wOther = wGv` (rearranging `r i = wGv + wOther`), a `G_v`-row.
  have hrhat : (∑ j, lam j • r j) = wGv := by rw [hlam_sum, hsum]; abel
  exact ⟨r, lam, i, hr, hrspan, hlam_i, hrhat ▸ hwGv, hlam_ne⟩

/-- **W5 — the redundancy-data packaging at the unpacked IH framework** (`lem:case-III-claim612-r`
infra, the `hcand`-discharge consumer-level redundancy extractor; Katoh–Tanigawa 2011 §6.4.1,
eqs. (6.18), (6.22)–(6.25), Phase 22h §1.50(b)/(f)). The form of `exists_redundant_panelRow_ab_lam`
the M₁/M₂/M₃ arms of the `hcand` discharge actually consume: the two `finrank` inputs of KT's
redundant-`ab`-row argument are supplied at their *natural* shape rather than as raw equations.

The eq.-(6.18) full-rank input `h618` is replaced by the realization-motive hypothesis `hrig`
(`Gab` is infinitesimally rigid on its own vertex set, `m = |V(Gab)|`): the rigidity-row span then
has dimension `D(m−1)` by the seed-rank bridge `finrank_span_rigidityRows_of_rigidOn` (W2, eq.
(6.18)).

The eq.-(6.22) input `h622` is replaced by the **lower bound** (KT's nested IH (6.1) at the
`k'`-dof `G_v`) plus the *free* upper bound. Defining `k' := D(m−1) − finrank(span R(G_v)-rows)`
makes `h622` (`finrank(span R(G_v)-rows) = D(m−1) − k'`) hold **by construction**, since the
`G_v`-row span sits inside the `G_{ab}`-row span (`span_rigidityRows_eq_sup_span_panelRow_edge` +
`finrank_mono`, the free upper bound `finrank(span R(G_v)-rows) ≤ D(m−1)`). The remaining hypothesis
`hk'` (`k' ≤ D − 2`) is precisely KT's eq.-(6.22) lower bound, carried here as the explicit named
crux `h622lb`:
\[ D(m-1) - (D-2) \;\le\; \operatorname{finrank}(\operatorname{span} R(G_v, q)\text{-rows}). \]

> **GAP 6 — adjudicated carry (user, 2026-06-10; Phase 22h Blockers).** `h622lb` is KT's nested
> induction hypothesis (6.1) applied to the minimal `k'`-dof `G_v` (`k' ≤ D − 2` via
> `splitOff_removeVertex_minimalKDof`), unreachable from the project's `0`-dof-only realization
> motive. It rides as this explicit hypothesis up through the `hcand` discharge and the Leaf-4/5
> wiring; 22h closes green-modulo this one inequality, discharged by a successor sub-phase that
> restructures the induction to KT's all-`k` motive.

The output is `exists_redundant_panelRow_ab_lam`'s redundancy data verbatim: the `(D − 1)`
independent `ab`-rows `r`, the unit-normalized coefficients `lam` (`lam i^* = 1`, KT eq. (6.25)),
the candidate vector `r̂ := ∑_j lam_j r_j` (KT eq. (6.27)) as a nonzero `G_v`-row member — the
`r̂ ≠ 0`
the Claim-6.12 disjunction needs and the `r̂ ∈ span R(G_v)-rows` the candidate-completion row
operation consumes. -/
theorem BodyHingeFramework.exists_redundant_panelRow_ab_lam_of_rigidOn
    [Finite α] {Gab Gv : Graph α β} {ends : β → α × α} {q : α × Fin (k + 2) → ℝ} {e₀ : β}
    (hD : 2 ≤ screwDim k)
    (huv : (ends e₀).1 ≠ (ends e₀).2)
    (hne₀ : (PanelHingeFramework.ofNormals Gab ends q).toBodyHinge.supportExtensor e₀ ≠ 0)
    (he₀ : Gab.IsLink e₀ (ends e₀).1 (ends e₀).2)
    (hle : ∀ e u v, Gv.IsLink e u v → Gab.IsLink e u v)
    (hsplit : ∀ e u v, Gab.IsLink e u v → Gv.IsLink e u v ∨ e = e₀)
    (hnev : Gab.vertexSet.Nonempty)
    (hrig : (PanelHingeFramework.ofNormals Gab ends q).toBodyHinge.IsInfinitesimallyRigidOn
      Gab.vertexSet)
    (h622lb : screwDim k * (Gab.vertexSet.ncard - 1) - (screwDim k - 2)
      ≤ Module.finrank ℝ (Submodule.span ℝ
          (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge.rigidityRows)) :
    ∃ (r : Fin (screwDim k - 1) → Module.Dual ℝ (α → ScrewSpace k)) (lam : Fin (screwDim k - 1) → ℝ)
      (i : Fin (screwDim k - 1)),
      LinearIndependent ℝ r ∧
      Submodule.span ℝ (Set.range r) = Submodule.span ℝ (Set.range (fun p :
        Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k =>
          (PanelHingeFramework.ofNormals Gab ends q).toBodyHinge.panelRow ends (e₀, p.1, p.2))) ∧
      lam i = 1 ∧
      (∑ j, lam j • r j) ∈ Submodule.span ℝ
        (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge.rigidityRows ∧
      (∑ j, lam j • r j) ≠ 0 := by
  set Fab := (PanelHingeFramework.ofNormals Gab ends q).toBodyHinge with hFab
  set Fv := (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge with hFv
  set m := Gab.vertexSet.ncard with hm
  -- Eq. (6.18): the rigid `Gab` framework has full rank `D(m − 1)` (W2, the seed-rank bridge). The
  -- framework graph is `Gab` definitionally, so its vertex set is `Gab.vertexSet`.
  have hgraph : Fab.graph = Gab := rfl
  have h618 : Module.finrank ℝ (Submodule.span ℝ Fab.rigidityRows) = screwDim k * (m - 1) := by
    have := Fab.finrank_span_rigidityRows_of_rigidOn (hgraph ▸ hnev) (hgraph ▸ hrig)
    rwa [hgraph] at this
  -- Eq. (6.22) by construction: set `k' := D(m − 1) − finrank(span R(G_v)-rows)`. The free upper
  -- bound `finrank(span R(G_v)-rows) ≤ D(m − 1)` (the `G_v`-row span sits in the `G_{ab}`-row span)
  -- makes the equation `finrank = D(m − 1) − k'` hold by omega.
  set fGv := Module.finrank ℝ (Submodule.span ℝ Fv.rigidityRows) with hfGv
  have hext : ∀ e, Fab.supportExtensor e = Fv.supportExtensor e := fun _ => rfl
  have hrow : Submodule.span ℝ Fab.rigidityRows
      = Submodule.span ℝ Fv.rigidityRows
        ⊔ Submodule.span ℝ (Set.range (fun p : Set.powersetCard (Fin (k + 2)) k
            × Set.powersetCard (Fin (k + 2)) k => Fab.panelRow ends (e₀, p.1, p.2))) :=
    Fab.span_rigidityRows_eq_sup_span_panelRow_edge Fv hext hne₀ he₀ hle hsplit
  have hub : fGv ≤ screwDim k * (m - 1) := by
    rw [hfGv, ← h618, hrow]; exact Submodule.finrank_mono le_sup_left
  set k' := screwDim k * (m - 1) - fGv with hk'def
  have h622 : fGv = screwDim k * (m - 1) - k' := by omega
  -- `hk' : k' ≤ D − 2` is exactly the carried eq.-(6.22) lower bound `h622lb` (GAP 6), rearranged.
  have hk' : k' ≤ screwDim k - 2 := by omega
  exact BodyHingeFramework.exists_redundant_panelRow_ab_lam (m := m) hD huv hne₀ he₀ hle hsplit
    hk' h618 h622

/-- **W6b — the candidate/bottom data packaging** (`lem:case-III-claim612-r` infra, the
`hcand`-discharge M₁/M₂ arms' input bundle; Katoh–Tanigawa 2011 §6.4.1, eqs. (6.23), (6.27), (6.29),
(6.30), Phase 22h §1.51(c)). From **one** invocation of W5's redundancy data
(`exists_redundant_panelRow_ab_lam_of_rigidOn`, KT p. 686: the *same* coefficients `λ_{(ab)j}` and
index `i^*` appear in (6.29) and (6.30)), produce the two ingredients the certify-then-rebase route
(§1.51(a)) consumes, both tied to that one `i^*`:

* the **candidate functional** `ρ` — KT's `r̂ = Σ_j λ_{(ab)j} r_j(q(ab))` read as a
  `ScrewSpace`-functional through `r̂ = hingeRow (ends e₀).1 (ends e₀).2 ρ`. Since
  `r̂ ∈ span (range r) = span {R(G_{ab}, q; (e₀)·)}` (the `e₀ = ab`-block) and that block is the
  `hingeRow`-image of the `(D−1)`-dimensional hinge-row block `r(p(e₀)) = (span C(e₀))^⊥`
  (`span_panelRow_edge_eq`), `r̂` factors as `hingeRow … ρ` with `ρ ∈ r(p(e₀))`, i.e.
  `ρ(C(e₀)) = 0` (`mem_hingeRowBlock_iff`). It is nonzero (`r̂ ≠ 0` and `hingeRow` linear in `ρ`),
  the discriminator's `hr`, and `hingeRow … ρ = r̂ ∈ span R(G_v, q)`-rows is W5's
  `r̂ ∈ span(G_v-rows)` re-read.

* the chosen `D(m−1)` **bottom rows** `w` of `R(G_v^{ab} ∖ (ab)i^*, q)` (KT eq. (6.23): that matrix
  is full rank `D(m−1)`, p. 685). Because `λ_{i^*} = 1`, `r i^* = r̂ − Σ_{j≠i^*} λ_j r_j` lies in
  `span(G_v-rows) ⊔ span(r '' {j ≠ i^*})`, so
  `span(R(G_v, q)-rows ∪ r '' {j ≠ i^*}) = span(R(G_{ab}, q)-rows)`
  (`span_rigidityRows_eq_sup_span_panelRow_edge` + `hrspan`), of finrank `D(m−1)` (W2, the
  `hgraph := rfl` idiom of W5). `Submodule.exists_fun_fin_finrank_span_eq` extracts an independent
  `w` of that size, each member per-tagged: a `G_v`-row, or an `r j'` member (`j' ≠ i^*`) — which,
  being in the `e₀`-block, is `hingeRow … ρ'` for some `ρ'(C(e₀)) = 0`.

**GAP 6 — adjudicated carry (user, 2026-06-10; §1.50(b) option (ii)).** This becomes W5's sole
caller, so KT's nested-IH lower bound `h622lb` (eq. (6.22) at the `k'`-dof `G_v`, unreachable from
the `0`-dof-only realization motive) enters the Lean *here*. It exits at the Leaf-4/5 wiring; 22h
closes green-modulo this one inequality (Phase 22h *Blockers*). -/
theorem BodyHingeFramework.exists_candidateRow_bottomRows_of_rigidOn
    [Finite α] {Gab Gv : Graph α β} {ends : β → α × α} {q : α × Fin (k + 2) → ℝ} {e₀ : β}
    (hD : 2 ≤ screwDim k)
    (huv : (ends e₀).1 ≠ (ends e₀).2)
    (hne₀ : (PanelHingeFramework.ofNormals Gab ends q).toBodyHinge.supportExtensor e₀ ≠ 0)
    (he₀ : Gab.IsLink e₀ (ends e₀).1 (ends e₀).2)
    (hle : ∀ e u v, Gv.IsLink e u v → Gab.IsLink e u v)
    (hsplit : ∀ e u v, Gab.IsLink e u v → Gv.IsLink e u v ∨ e = e₀)
    (hnev : Gab.vertexSet.Nonempty)
    (hrig : (PanelHingeFramework.ofNormals Gab ends q).toBodyHinge.IsInfinitesimallyRigidOn
      Gab.vertexSet)
    (h622lb : screwDim k * (Gab.vertexSet.ncard - 1) - (screwDim k - 2)
      ≤ Module.finrank ℝ (Submodule.span ℝ
          (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge.rigidityRows)) :
    ∃ (ρ : Module.Dual ℝ (ScrewSpace k))
      (w : Fin (screwDim k * (Gab.vertexSet.ncard - 1)) → Module.Dual ℝ (α → ScrewSpace k)),
      ρ ≠ 0 ∧
      ρ ((PanelHingeFramework.ofNormals Gab ends q).toBodyHinge.supportExtensor e₀) = 0 ∧
      BodyHingeFramework.hingeRow (ends e₀).1 (ends e₀).2 ρ ∈ Submodule.span ℝ
        (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge.rigidityRows ∧
      LinearIndependent ℝ w ∧
      (∀ j, w j ∈ (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge.rigidityRows ∨
        ∃ ρ' : Module.Dual ℝ (ScrewSpace k),
          ρ' ((PanelHingeFramework.ofNormals Gab ends q).toBodyHinge.supportExtensor e₀) = 0 ∧
          w j = BodyHingeFramework.hingeRow (ends e₀).1 (ends e₀).2 ρ') := by
  classical
  set Fab := (PanelHingeFramework.ofNormals Gab ends q).toBodyHinge with hFab
  set Fv := (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge with hFv
  set m := Gab.vertexSet.ncard with hm
  -- W5: the `(D − 1)` independent `ab`-rows `r`, unit-normalized coefficients `lam` (`lam i = 1`),
  -- and the candidate `r̂ := ∑_j λ_j r_j` as a nonzero member of `span (R(G_v)-rows)`.
  obtain ⟨r, lam, i, hr, hrspan, hlam_i, hrhat_mem, hrhat_ne⟩ :=
    BodyHingeFramework.exists_redundant_panelRow_ab_lam_of_rigidOn (Gab := Gab) (Gv := Gv)
      (ends := ends) (q := q) (e₀ := e₀) hD huv hne₀ he₀ hle hsplit hnev hrig h622lb
  -- The `e₀`-block `E_b = span (range r) = span {R(G_{ab}, q; (e₀)·)}`, the `hingeRow`-image of the
  -- `(D−1)`-dimensional hinge-row block `r(p(e₀))` (`span_panelRow_edge_eq`).
  set Eb := Submodule.span ℝ (Set.range r) with hEb
  have hEb' : Eb = Submodule.map (screwDiff (ends e₀).1 (ends e₀).2).dualMap
      (Fab.hingeRowBlock e₀) := by rw [hrspan, Fab.span_panelRow_edge_eq e₀ hne₀]
  set rhat := ∑ j, lam j • r j with hrhat
  -- `r̂ ∈ E_b = map (screwDiff …).dualMap (r(p(e₀)))`, so `r̂ = hingeRow … ρ`, `ρ` in the block.
  have hrhat_Eb : rhat ∈ Eb := by
    rw [hrhat]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  rw [hEb', Submodule.mem_map] at hrhat_Eb
  obtain ⟨ρ, hρ_blk, hρ⟩ := hrhat_Eb
  rw [← BodyHingeFramework.hingeRow_eq_dualMap] at hρ
  -- `ρ(C(e₀)) = 0` (block membership), and `ρ ≠ 0` (else `r̂ = hingeRow … 0 = 0`).
  have hρe₀ : ρ (Fab.supportExtensor e₀) = 0 := (Fab.mem_hingeRowBlock_iff e₀ ρ).1 hρ_blk
  have hρne : ρ ≠ 0 := by
    rintro rfl
    rw [BodyHingeFramework.hingeRow, LinearMap.zero_comp] at hρ
    exact hrhat_ne hρ.symm
  -- The candidate-row span membership: `hingeRow … ρ = r̂ ∈ span (R(G_v)-rows)`.
  have hρGv : BodyHingeFramework.hingeRow (ends e₀).1 (ends e₀).2 ρ
      ∈ Submodule.span ℝ Fv.rigidityRows := hρ.symm ▸ hrhat_mem
  -- The bottom-row generating set: `R(G_v, q)-rows ∪ r '' {j ≠ i^*}`, whose span is the full
  -- `R(G_{ab}, q)`-row span (`r i^* = r̂ − ∑_{j≠i^*} λ_j r_j`, both addends in the union's span).
  set S := Fv.rigidityRows ∪ r '' {j | j ≠ i} with hS
  have hext : ∀ e, Fab.supportExtensor e = Fv.supportExtensor e := fun _ => rfl
  have hrow : Submodule.span ℝ Fab.rigidityRows
      = Submodule.span ℝ Fv.rigidityRows ⊔ Eb := by
    rw [hrspan]
    exact Fab.span_rigidityRows_eq_sup_span_panelRow_edge Fv hext hne₀ he₀ hle hsplit
  -- `r̂ = ∑_j λ_j r_j = r i^* + ∑_{j ≠ i^*} λ_j r_j` (since `λ_{i^*} = 1`), so
  -- `r i^* = r̂ − ∑_{j≠i^*} λ_j r_j`.
  have hri : r i = rhat - ∑ j ∈ Finset.univ.erase i, lam j • r j := by
    rw [hrhat, Finset.sum_erase_eq_sub (Finset.mem_univ i), hlam_i, one_smul]; abel
  have hSspan : Submodule.span ℝ S = Submodule.span ℝ Fab.rigidityRows := by
    rw [hS, Submodule.span_union, hrow, hEb]
    refine le_antisymm (sup_le_sup_left ?_ _) (sup_le le_sup_left ?_)
    · -- `span (r '' {≠ i}) ≤ span (range r) = E_b`.
      rw [Submodule.span_le]
      rintro _ ⟨j, _, rfl⟩; exact Submodule.subset_span ⟨j, rfl⟩
    · -- `span (range r) ≤ span (R(G_v)-rows) ⊔ span (r '' {≠ i})`: `r i^*` is the only generator
      -- not already in `span (r '' {≠ i})`, and it equals `r̂ − ∑_{≠ i^*}` ∈ the join.
      rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      by_cases hji : j = i
      · subst hji
        rw [hri]
        refine Submodule.sub_mem _ (Submodule.mem_sup_left hrhat_mem) (Submodule.mem_sup_right ?_)
        exact Submodule.sum_mem _ fun j' hj' => Submodule.smul_mem _ _ <| Submodule.subset_span
          ⟨j', Finset.ne_of_mem_erase hj', rfl⟩
      · exact Submodule.mem_sup_right (Submodule.subset_span ⟨j, hji, rfl⟩)
  haveI : Fintype α := Fintype.ofFinite α
  -- The span has finrank `D(m − 1)` (W2 at the rigid `Gab`; the `hgraph := rfl` idiom of W5).
  have hgraph : Fab.graph = Gab := rfl
  have hfin : Module.finrank ℝ (Submodule.span ℝ S) = screwDim k * (m - 1) := by
    rw [hSspan]
    have := Fab.finrank_span_rigidityRows_of_rigidOn (hgraph ▸ hnev) (hgraph ▸ hrig)
    rwa [hgraph] at this
  -- Extract `D(m − 1)` independent members of `S`; per-tag each as a `G_v`-row or an `r j'`-row.
  obtain ⟨w₀, hw₀mem, _, hw₀indep⟩ := Submodule.exists_fun_fin_finrank_span_eq ℝ S
  -- Re-index from `Fin (finrank …)` to `Fin (D(m−1))` along `hfin`.
  refine ⟨ρ, fun j => w₀ (Fin.cast hfin.symm j), hρne, hρe₀, hρGv,
    hw₀indep.comp _ (Fin.cast_injective _), fun j => ?_⟩
  rcases hw₀mem (Fin.cast hfin.symm j) with hv | ⟨j', _, hj'⟩
  · exact Or.inl hv
  · -- An `r j'`-tagged member: `r j' ∈ span (range r) = E_b`, the `hingeRow`-image of `r(p(e₀))`.
    refine Or.inr ?_
    have hrj'_Eb : r j' ∈ Eb := Submodule.subset_span ⟨j', rfl⟩
    rw [hEb', Submodule.mem_map] at hrj'_Eb
    obtain ⟨ρ', hρ'_blk, hρ'⟩ := hrj'_Eb
    rw [← BodyHingeFramework.hingeRow_eq_dualMap] at hρ'
    exact ⟨ρ', (Fab.mem_hingeRowBlock_iff e₀ ρ').1 hρ'_blk, (hρ'.trans hj').symm⟩

/-- **KT eq. (6.43): the `a`-column block of the eq. (6.24) vanishing combination is `0`**
(`lem:case-III-candidate-row` infra, the candidate-completion's eq. (6.43); Katoh–Tanigawa 2011
§6.4.1, eq. (6.43), Phase 22e). The eq. (6.24)/(6.25) decomposition
(`exists_redundant_panelRow_ab_decomposition`) records the redundant `ab`-row as
`r i^* = wGv + wOther`, i.e.\ the *vanishing combination*
`g := wGv + wOther - r i^* = 0` — KT's eq. (6.24)
`Σ_j λ_{(ab)j} R(G_v^{ab}, q; (ab)j) + Σ_{e ∈ E_v, j} λ_{ej} R(G_v^{ab}, q; ej) = 0`
as a functional on the screw assignments `α → ScrewSpace k`. KT eq. (6.43) is its
**restriction to any single body `a`'s screw column**: precomposing the zero functional `g`
with the column injection `single a : ScrewSpace k → (α → ScrewSpace k)` (place a screw on body
`a`, `0` elsewhere) is again `0`,
\[ g \circ \mathrm{single}_a \;=\; 0 \quad\text{on } \mathrm{ScrewSpace}\,k, \]
concretely `Σ_{e ∈ E_v ∪ \{ab\}, j} λ_{ej} R(G_v^{ab}, q; e_j, a) = 0` (KT eq. (6.43)).

This is the one fact the candidate-completion transport (`lem:case-III-candidate-row`, eqs.
(6.26)–(6.28)) still needs to certify that the transported row `w`'s `V ∖ {v}` part vanishes:
at the degenerate eq. (6.12) placement `p_1` the `(ab)j`-rows become `(vb)j`-rows, and over
`V ∖ {v}` the two differ by exactly the `a`-column block `r_j(·\,a)` of the `ab`-edge (the
`(vb)`-hinge is `0` in column `a`). So `w`'s `V ∖ {v}` part is the eq. (6.24) sum (`= g(S) = 0`)
minus the residual `a`-block, which this lemma kills. The `a`-block reads off the column-`a`
content of every term in the combination — `single a` evaluates each `hingeRow`-row at the screw
placed on `a` — so the residual is exactly `g ∘ single a`, zero because `g` is the zero
functional. Stated for *every* body `a` (the transport instantiates it at the `ab`-edge's surviving
endpoint). The companion column-support core `dualMap_eq_comp_single_proj_of_vanish_off`
(eq. (6.28)) then turns `w` (now `V ∖ {v}`-zero) into the pure `v`-column row of eq. (6.29). -/
theorem BodyHingeFramework.exists_redundant_panelRow_ab_decomposition_acolumn_zero
    [Finite α] [DecidableEq α] {Gab Gv : Graph α β} {ends : β → α × α}
    {q : α × Fin (k + 2) → ℝ} {e₀ : β}
    (hD : 2 ≤ screwDim k)
    (huv : (ends e₀).1 ≠ (ends e₀).2)
    (hne₀ : (PanelHingeFramework.ofNormals Gab ends q).toBodyHinge.supportExtensor e₀ ≠ 0)
    (he₀ : Gab.IsLink e₀ (ends e₀).1 (ends e₀).2)
    (hle : ∀ e u v, Gv.IsLink e u v → Gab.IsLink e u v)
    (hsplit : ∀ e u v, Gab.IsLink e u v → Gv.IsLink e u v ∨ e = e₀)
    {m k' : ℕ} (hk' : k' ≤ screwDim k - 2)
    (h618 : Module.finrank ℝ (Submodule.span ℝ
        (PanelHingeFramework.ofNormals Gab ends q).toBodyHinge.rigidityRows)
      = screwDim k * (m - 1))
    (h622 : Module.finrank ℝ (Submodule.span ℝ
        (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge.rigidityRows)
      = screwDim k * (m - 1) - k') :
    ∃ (r : Fin (screwDim k - 1) → Module.Dual ℝ (α → ScrewSpace k)),
      LinearIndependent ℝ r ∧
      Submodule.span ℝ (Set.range r) = Submodule.span ℝ (Set.range (fun p :
        Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k =>
          (PanelHingeFramework.ofNormals Gab ends q).toBodyHinge.panelRow ends (e₀, p.1, p.2))) ∧
      ∃ (i : Fin (screwDim k - 1))
        (wGv wOther : Module.Dual ℝ (α → ScrewSpace k)),
        wGv ∈ Submodule.span ℝ
          (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge.rigidityRows ∧
        wOther ∈ Submodule.span ℝ (r '' {j | j ≠ i}) ∧
        r i = wGv + wOther ∧
        ∀ a : α, (wGv + wOther - r i).comp
            (LinearMap.single ℝ (fun _ : α => ScrewSpace k) a) = 0 := by
  obtain ⟨r, hr, hrspan, i, wGv, wOther, hwGv, hwOther, hsum⟩ :=
    BodyHingeFramework.exists_redundant_panelRow_ab_decomposition hD huv hne₀ he₀ hle hsplit hk'
      h618 h622
  -- The combination `wGv + wOther - r i` is the zero functional (`r i = wGv + wOther`); its
  -- restriction to any body `a`'s screw column (precompose with `single a`) is therefore `0`.
  refine ⟨r, hr, hrspan, i, wGv, wOther, hwGv, hwOther, hsum, fun a => ?_⟩
  rw [hsum, sub_self, LinearMap.zero_comp]

/-- **The eq. (6.27) per-row transport collapse: the `vb`-row minus the `ab`-row is a `va`-hinge
row** (`lem:case-III-candidate-row`, the eqs. (6.26)–(6.27) transport step; Katoh–Tanigawa 2011
§6.4.1, eq. (6.27), Phase 22e). At the degenerate eq. (6.12) placement `q₀` — `v`'s normal placed
at `n_a + t • n_b` (`hq₀v`), with `q₀` agreeing with the inductive seed `q` at the surviving
endpoint `b` (`hq₀b`; the `ab`-row reads `q` at `a` directly) — the transported `(vb)j`-row of
`R(G, q₀)` reproduces the
`(ab)j`-row of `R(G_v^{ab}, q)` *up to its endpoint*: both read the **same** supporting extensor
`C = panelSupportExtensor n_a n_b` (the shear identity `panelSupportExtensor_add_smul_right` makes
`v`'s `vb`-extensor equal `q`'s `ab`-extensor, KT eq. (6.16)), so they are
`hingeRow v b (annihRow C t₁ t₂)` and `hingeRow a b (annihRow C t₁ t₂)`. Their difference is the
pure `va`-hinge row
\[ R(G, q₀; (vb)j) - R(G_v^{ab}, q; (ab)j)
   = \mathrm{hingeRow}\ v\ a\ (\mathrm{annihRow}\ C\ t₁\ t₂), \]
by the hinge-difference collapse `hingeRow_sub_hingeRow_eq`
(`(S_v - S_b) - (S_a - S_b) = S_v - S_a`).

This is the per-row form of KT eq. (6.27): transporting the redundant-`ab`-row combination
(`exists_redundant_panelRow_ab_decomposition`, the `λ_{(ab)j}`-weighted `ab`-rows with
`λ_{(ab)i^*} = 1`) up to `R(G, q₀)` as `(vb)j`-rows and subtracting the inductive `ab`-combination
(which the eq. (6.24) decomposition makes vanish, `r i^* = w_{Gv} + w_{Other}`) collapses the
transported row to `w = hingeRow v a ρ_g` with `ρ_g = Σ_j λ_{(ab)j} (annihRow C ·)`. The column op
`columnOp` then turns this `va`-hinge row into the pure-`v`-column row of eq. (6.28)
(`comp_columnOp_eq_comp_single_proj`), the `+1` row the eq. (6.29) pin-block
(`linearIndependent_sum_pinned_block_augment`) consumes. -/
theorem PanelHingeFramework.panelRow_vb_sub_panelRow_ab_eq_hingeRow_va
    (G Gab : Graph α β) (ends : β → α × α) {q₀ q : α × Fin (k + 2) → ℝ}
    {e_b e₀ : β} {v a b : α} {t : ℝ}
    (hends_eb : ends e_b = (v, b)) (hends_e0 : ends e₀ = (a, b))
    (hq₀v : (fun i => q₀ (v, i)) = (fun i => q (a, i)) + t • (fun i => q (b, i)))
    (hq₀b : (fun i => q₀ (b, i)) = fun i => q (b, i))
    (t₁ t₂ : Set.powersetCard (Fin (k + 2)) k) :
    (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.panelRow ends (e_b, t₁, t₂)
        - (PanelHingeFramework.ofNormals Gab ends q).toBodyHinge.panelRow ends (e₀, t₁, t₂)
      = BodyHingeFramework.hingeRow v a (annihRow
          (panelSupportExtensor (fun i => q (a, i)) (fun i => q (b, i))) t₁ t₂) := by
  -- Both panel rows read the *same* supporting extensor `C = panelSupportExtensor n_a n_b`: at `q₀`
  -- the `vb`-extensor is `panelSupportExtensor (n_a + t•n_b) n_b = panelSupportExtensor n_a n_b`
  -- (the shear identity, KT eq. (6.16)); at `q` the `ab`-extensor is the same.
  simp only [BodyHingeFramework.panelRow, PanelHingeFramework.toBodyHinge_supportExtensor,
    PanelHingeFramework.ofNormals_ends, PanelHingeFramework.ofNormals_normal,
    hends_eb, hends_e0, hq₀v, hq₀b]
  rw [panelSupportExtensor_add_smul_right]
  -- The two rows are now `hingeRow v b (annihRow C ·)` and `hingeRow a b (annihRow C ·)`; their
  -- difference is the pure `va`-hinge row (`(S_v − S_b) − (S_a − S_b) = S_v − S_a`).
  exact BodyHingeFramework.hingeRow_sub_hingeRow_eq v a b _

/-- **The candidate-completion row operation: the missing `+1` row `w`**
(`lem:case-III-candidate-row`, the eqs. (6.24)–(6.28) producer; Katoh–Tanigawa 2011 §6.4.1,
eqs. (6.24)–(6.28), Phase 22e). The combination-level threading that converts KT Claim 6.11's
redundant `ab`-row (eq. (6.23)) into the missing full-rank row of eq. (6.29). The input is the
*common* element `wGv` of the eq.-(6.24)/(6.25) decomposition: the `G_v`-row part of the redundant
`ab`-row, which lies in the `ab`-block `span {R(G_v^{ab}, q; (ab)·)}` (`hwGv_ab`, since
`wGv = r i^* − wOther` with both terms in the block).

By the per-edge block identity (`span_panelRow_edge_eq`) the `ab`-block is the `hingeRow a b`-image
of the `(D − 1)`-dimensional hinge-row block `r(p(e₀)) = (\mathrm{span}\,C)^\perp`
(`C = \mathrm{panelSupportExtensor}\,n_a\,n_b`), so `wGv = \mathrm{hingeRow}\,a\,b\,ρ` for some
`ρ ∈ r(p(e₀))`. The eq.-(6.12) seed reproduces the `ab`-extensor at `v`'s `b`-hinge `e_b`
(`panelSupportExtensor_add_smul_right`, KT eq. (6.16)), so `ρ` is also a hinge-row-block functional
of `R(G, q₀)`'s `e_b = vb`-hinge: `\mathrm{hingeRow}\,v\,b\,ρ` is the transported `(vb)i^*`-row,
a genuine rigidity row of `R(G, q₀)`. Its eq.-(6.27) collapse against the inductive `(ab)`-part is
the pure `(va)`-hinge candidate row `w`,
\[ \mathrm{hingeRow}\,v\,b\,ρ \;-\; w_{\mathrm{Gv}} \;=\; \mathrm{hingeRow}\,v\,a\,ρ \;=\; w, \]
since `wGv = \mathrm{hingeRow}\,a\,b\,ρ` and `(S_v − S_b) − (S_a − S_b) = S_v − S_a`
(`hingeRow_sub_hingeRow_eq`). The companion `comp_columnOp_eq_comp_single_proj` then turns `w` into
the pure-`v`-column row the eq.-(6.29) pin-block (`linearIndependent_sum_pinned_block_augment`)
consumes: operating by `columnOp` (`col_a += col_v`, KT eqs. (6.14)–(6.15)) makes `w ∘ Φ` depend
only on `v`'s screw column — the missing `+1` lifting the stratum-1 brick `D(|V|−1) − 1`
(`case_II_placement_eq612`) to full `D(|V|−1)`. -/
theorem PanelHingeFramework.exists_candidate_row_eq612 [Finite α]
    (G Gab : Graph α β) (ends : β → α × α) {q : α × Fin (k + 2) → ℝ}
    {e₀ e_b : β} {v a b : α} {t : ℝ}
    (hends_e0 : ends e₀ = (a, b)) (hends_eb : ends e_b = (v, b))
    (hG_eb : G.IsLink e_b v b)
    (q₀ : α × Fin (k + 2) → ℝ)
    (hq₀v : (fun i => q₀ (v, i)) = (fun i => q (a, i)) + t • (fun i => q (b, i)))
    (hq₀b : (fun i => q₀ (b, i)) = fun i => q (b, i))
    (hne₀ : (PanelHingeFramework.ofNormals Gab ends q).toBodyHinge.supportExtensor e₀ ≠ 0)
    {wGv : Module.Dual ℝ (α → ScrewSpace k)}
    (hwGv_ab : wGv ∈ Submodule.span ℝ (Set.range (fun p :
        Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k =>
          (PanelHingeFramework.ofNormals Gab ends q).toBodyHinge.panelRow ends (e₀, p.1, p.2)))) :
    ∃ ρ : Module.Dual ℝ (ScrewSpace k),
      wGv = BodyHingeFramework.hingeRow a b ρ ∧
      -- the transported `(vb)i^*`-row is a genuine rigidity row of `R(G, q₀)` (KT eq. (6.26))
      BodyHingeFramework.hingeRow v b ρ
        ∈ (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.rigidityRows ∧
      -- its eq.-(6.27) collapse against the inductive `(ab)`-part is the candidate row `va`-hinge
      BodyHingeFramework.hingeRow v b ρ - wGv = BodyHingeFramework.hingeRow v a ρ := by
  set Fab := (PanelHingeFramework.ofNormals Gab ends q).toBodyHinge with hFab
  set FG := (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge with hFG
  -- The `ab`-block is the `hingeRow a b`-image of the hinge-row block `(span C)^⊥` at `e₀`.
  rw [Fab.span_panelRow_edge_eq e₀ hne₀, hends_e0] at hwGv_ab
  obtain ⟨ρ, hρ_blk, hρ⟩ := hwGv_ab
  -- `(screwDiff a b).dualMap ρ = hingeRow a b ρ` (definitional) recovers `wGv`.
  rw [← BodyHingeFramework.hingeRow_eq_dualMap] at hρ
  refine ⟨ρ, hρ.symm, ?_, ?_⟩
  · -- `hingeRow v b ρ` is a rigidity row of `R(G, q₀)`: witness the link `e_b` and `ρ`'s block.
    refine ⟨e_b, v, b, hG_eb, ρ, ?_, rfl⟩
    -- `hingeRowBlock` reads only the support extensor; at `q₀` the `e_b`-extensor equals `C(e₀)`.
    rw [BodyHingeFramework.hingeRowBlock_apply] at hρ_blk ⊢
    have hCeq : FG.supportExtensor e_b = Fab.supportExtensor e₀ := by
      rw [hFG, hFab, PanelHingeFramework.toBodyHinge_supportExtensor,
        PanelHingeFramework.toBodyHinge_supportExtensor, PanelHingeFramework.ofNormals_ends,
        PanelHingeFramework.ofNormals_ends, PanelHingeFramework.ofNormals_normal,
        PanelHingeFramework.ofNormals_normal, PanelHingeFramework.ofNormals_normal,
        PanelHingeFramework.ofNormals_normal, hends_eb, hends_e0, hq₀v, hq₀b,
        panelSupportExtensor_add_smul_right]
    rw [hCeq]; exact hρ_blk
  · -- The collapse: `hingeRow v b ρ − hingeRow a b ρ = hingeRow v a ρ`.
    rw [← hρ]
    exact BodyHingeFramework.hingeRow_sub_hingeRow_eq v a b ρ

/-- **L1 — the inductive old/new panel-row blocks of the `d = 3` candidate placement**
(`lem:case-II-realization` / `lem:case-III`, the IH-extraction leaf of the `hsplit` producer;
Katoh–Tanigawa 2011 §6.4.1, eq. (6.12), Phase 22g). The first leaf discharging the L0 skeleton's
carried `panelRow`-packaging: from the inductively rigid split-off block `ofNormals Gv ends q`
(rigid on `V(Gv) = V(G) ∖ {v}`, transversal hinges, the `e₀ = ab`-hinge transversal `hgab`), at the
shared seed `q₀` that overrides body `v`'s normal by `n_a + t·n_b` (the eq. (6.12) shear, `t ≠ 0`),
it produces the **two blocks** the three candidate producers
(`linearIndependent_sum_{augment,p2,p3}_candidateRow`) consume:

* the **OLD block** `so` — `D(|V(Gv)|−1) = D(|V(G)|−1) − D` independent linking panel rows of
  `ofNormals G ends q₀`, transported off the IH-rigid `Gv`-block (N7b-0 `…_of_rigidOn_linking` +
  the graph-free transport `…_panelRow_transport`, `panelRow` reading only `ends`/`q₀`); they vanish
  through body `v`'s screw column (`hold`, their `Gv`-edges avoiding `v`) and stay independent
  (`holdindep`) — the producers' `hold`/`holdindep` inputs.
* the **NEW block** `sn` — the `D − 1` independent panel rows of the re-inserted body `v`'s
  hinge `e_b` (N7b-1 `…_subfamily_of_edge`), all using `e_b` (`hsn_e`), independent (`hsn_indep`),
  and staying independent through `v = (ends e_b).1`'s screw column (`hnewpin`,
  `…_comp_single_of_edge`) — the producers' `rn`/`hrnpin` input (the full hinge-block span `hspan`
  they additionally need is L2's bridge).

Plus the two extensor-nonzero facts L3 reuses: the `va`-hinge `e_a` is a nondegenerate line
`L ⊂ Π(a)` (`hane`, KT eq. (6.12)'s candidate, `t ≠ 0`) and the reproduced `vb`-hinge `e_b` is
transversal (`hnewne`). This is the front of `case_II_placement_eq612` (which packages the same two
blocks into one `D(|V(G)|−1) − 1`-size set); L1 exposes them separately so each candidate placement
appends its own `+1` candidate row. -/
theorem PanelHingeFramework.case_III_old_new_blocks [DecidableEq α] [Finite α] [Finite β]
    (G Gv : Graph α β) (ends : β → α × α)
    {v a b : α} {e_a e_b : β} (hvVc : v ∉ V(Gv)) (haVc : a ∈ V(Gv)) (hbVc : b ∈ V(Gv))
    (_hG_eb : G.IsLink e_b v b) (hends_eb : ends e_b = (v, b))
    (_hG_ea : G.IsLink e_a v a) (hends_ea : ends e_a = (v, a))
    {q : α × Fin (k + 2) → ℝ}
    (hends_Gv : ∀ e u w, Gv.IsLink e u w → Gv.IsLink e (ends e).1 (ends e).2)
    (hne_Gv : ∀ e, Gv.IsLink e (ends e).1 (ends e).2 →
      (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge.supportExtensor e ≠ 0)
    (hrig : (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge.IsInfinitesimallyRigidOn V(Gv))
    {t : ℝ} (ht : t ≠ 0)
    (q₀ : α × Fin (k + 2) → ℝ)
    (hq₀ : q₀ = fun p => if p.1 = v then
        ((fun i => q (a, i)) + t • (fun i => q (b, i))) p.2 else q p)
    (hgab : LinearIndependent ℝ ![(fun i => q (a, i)), (fun i => q (b, i))]) :
    -- `v`'s `a`-hinge nondegeneracy (the `va`-line `L ⊂ Π(a)`, KT eq. (6.12), `t ≠ 0`) and the
    -- reproduced `vb`-hinge transversal (the new block sits on it).
    (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.supportExtensor e_a ≠ 0 ∧
    (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.supportExtensor e_b ≠ 0 ∧
    -- the OLD block `so`: `D(|V(Gv)|−1)` independent linking rows, vanishing at `v`'s column.
    ∃ so : Set (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k),
      Nat.card so = screwDim k * (V(Gv).ncard - 1) ∧
      LinearIndependent ℝ (fun i : so =>
        (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.panelRow ends (i : β × _ × _)) ∧
      (∀ (j : so) (x : ScrewSpace k),
        (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.panelRow ends (j : β × _ × _)
          (Function.update (0 : α → ScrewSpace k) v x) = 0) ∧
      (∀ i ∈ so, (i : β × _ × _).1 ≠ e_b) ∧
    -- the NEW block `sn`: the `D − 1` independent `e_b`-rows, staying independent through `v`'s
    -- column (`hnewpin`).
    ∃ sn : Set (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k),
      (∀ i ∈ sn, (i : β × _ × _).1 = e_b) ∧ Nat.card sn = screwDim k - 1 ∧
      LinearIndependent ℝ (fun i : sn =>
        (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.panelRow ends (i : β × _ × _)) ∧
      LinearIndependent ℝ (fun i : sn =>
        ((PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.panelRow ends
          (i : β × _ × _)).comp
          (LinearMap.single ℝ (fun _ : α => ScrewSpace k) v)) := by
  classical
  haveI : Fintype α := Fintype.ofFinite α
  set FG := (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge with hFG
  set n_a : Fin (k + 2) → ℝ := fun i => q (a, i) with hn_a
  set n_b : Fin (k + 2) → ℝ := fun i => q (b, i) with hn_b
  -- (1) The shared seed is the IH seed with `v`'s normal overridden by `n_a + t • n_b`, so the IH
  -- rigidity transports to `q₀` (overriding the fresh `v ∉ V(Gᵥ)` leaves the `Gᵥ`-block untouched).
  have hqeq : (fun p => if p.1 = v then ((n_a + t • n_b) : Fin (k + 2) → ℝ) p.2 else q p) = q₀ := by
    rw [hq₀]
  have hwN : PanelHingeFramework.ofNormals Gv ends q₀
      = (PanelHingeFramework.ofNormals Gv ends q).withNormal v (n_a + t • n_b) := by
    rw [← hqeq]
    exact PanelHingeFramework.ofNormals_update_eq_withNormal Gv ends q v (n_a + t • n_b)
  -- No `Gᵥ`-edge touches `v` (its endpoints lie in `V(Gᵥ)`, and `v ∉ V(Gᵥ)`).
  have hvedge : ∀ e u w, Gv.IsLink e u w → (ends e).1 ≠ v ∧ (ends e).2 ≠ v := by
    intro e u w he
    have hl := hends_Gv e u w he
    exact ⟨fun h => hvVc (h ▸ hl.left_mem), fun h => hvVc (h ▸ hl.right_mem)⟩
  -- The motion space is unchanged when overriding the unhinged `v`, so the IH rigidity transports.
  have hZeq : (PanelHingeFramework.ofNormals Gv ends q₀).toBodyHinge.infinitesimalMotions
      = (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge.infinitesimalMotions := by
    rw [hwN]
    exact (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge_withNormal_infinitesimalMotions_eq
      v (n_a + t • n_b) hvedge
  have hrig₀ :
      (PanelHingeFramework.ofNormals Gv ends q₀).toBodyHinge.IsInfinitesimallyRigidOn V(Gv) := by
    intro S hS u hu w hw
    refine hrig S ?_ u hu w hw
    rw [← BodyHingeFramework.mem_infinitesimalMotions, ← hZeq,
      BodyHingeFramework.mem_infinitesimalMotions] at *
    exact hS
  -- The `Gᵥ`-hinges stay transversal at `q₀` (endpoints avoid `v`, where `q₀` agrees with `q`).
  have hne₀ : ∀ e, Gv.IsLink e (ends e).1 (ends e).2 →
      (PanelHingeFramework.ofNormals Gv ends q₀).toBodyHinge.supportExtensor e ≠ 0 := by
    intro e he
    obtain ⟨h₁, h₂⟩ := hvedge e _ _ he
    rw [hwN, (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge_withNormal_supportExtensor_of_ne
      v (n_a + t • n_b) e (by simpa using h₁) (by simpa using h₂)]
    exact hne_Gv e he
  -- (2) OLD block (N7b-0, `_linking`): the rigid `Gᵥ`-realization carries `D(|V(Gᵥ)|−1)`
  -- independent linking panel rows of `ofNormals Gv ends q₀`.
  have hVGvne : V(Gv).Nonempty := ⟨b, hbVc⟩
  set FGv := (PanelHingeFramework.ofNormals Gv ends q₀).toBodyHinge with hFGv
  obtain ⟨so, hso_link, hso_card, hso_indep⟩ :=
    FGv.exists_independent_panelRow_subfamily_of_rigidOn_linking (ends := ends)
      (by simpa [hFGv] using hends_Gv) (by simpa [hFGv] using hne₀) (by simpa [hFGv] using hVGvne)
      (by simpa [hFGv] using hrig₀)
  -- (3) Transport the old block onto `G` (N7b-2; `panelRow` reads only `ends`/`q₀`, not the graph,
  -- so `hrow := rfl`).
  have hso_indep_G : LinearIndependent ℝ (fun i : so =>
      FG.panelRow ends (i : β × _ × _)) :=
    PanelHingeFramework.exists_independent_panelRow_transport Gv G ends ends q₀ q₀
      (f := id) Function.injective_id (fun i => rfl) hso_indep
  -- The re-inserted body `v` and its neighbour `b` are distinct (`b ∈ V(Gᵥ)`, `v ∉ V(Gᵥ)`).
  have hvb : v ≠ b := fun h => hvVc (h ▸ hbVc)
  -- The shared seed reads `q₀(v,·) = n_a + t·n_b` and `q₀(b,·) = n_b`.
  have hq₀v : (fun i => q₀ (v, i)) = n_a + t • n_b := by
    funext i; rw [hq₀]; simp
  have hq₀b : (fun i => q₀ (b, i)) = n_b := by
    funext i; rw [hq₀, hn_b]; simp only [if_neg hvb.symm]
  have hva : v ≠ a := fun h => hvVc (h ▸ haVc)
  have hq₀a : (fun i => q₀ (a, i)) = n_a := by
    funext i; rw [hq₀, hn_a]; simp only [if_neg hva.symm]
  -- The `va`-hinge `e_a` stays a nondegenerate line `L ⊂ Π(a)` (KT eq. (6.12), `t ≠ 0`).
  have hane : FG.supportExtensor e_a ≠ 0 := by
    rw [PanelHingeFramework.toBodyHinge_supportExtensor, PanelHingeFramework.ofNormals_ends,
      PanelHingeFramework.ofNormals_normal, PanelHingeFramework.ofNormals_normal, hends_ea]
    simp only [hq₀v, hq₀a, panelSupportExtensor_add_smul_left]
    exact smul_ne_zero (neg_ne_zero.mpr ht) ((panelSupportExtensor_ne_zero_iff n_a n_b).mpr hgab)
  -- (4) NEW block (N7b-1): the reproduced `vb`-hinge `e_b` is transversal
  -- (`panelSupportExtensor_add_smul_right` reproduces the transversal `e₀ = ab`-hinge), giving
  -- `D − 1` independent new rows.
  have hnewne : FG.supportExtensor e_b ≠ 0 := by
    rw [PanelHingeFramework.toBodyHinge_supportExtensor, PanelHingeFramework.ofNormals_ends,
      PanelHingeFramework.ofNormals_normal, PanelHingeFramework.ofNormals_normal, hends_eb]
    simp only [hq₀v, hq₀b, panelSupportExtensor_add_smul_right]
    exact (panelSupportExtensor_ne_zero_iff n_a n_b).mpr hgab
  have hev : (ends e_b).2 ≠ (ends e_b).1 := by rw [hends_eb]; exact hvb.symm
  obtain ⟨sn, hsn_e, hsn_card, hsn_indep⟩ :=
    FG.exists_independent_panelRow_subfamily_of_edge
      (ends := ends) (e := e_b) (by rw [hends_eb]; exact hvb) hnewne
  -- `hnewpin`: the new rows stay independent through `v = (ends e_b).1`'s screw column.
  have hnewpin := FG.linearIndependent_panelRow_comp_single_of_edge
    (ends := ends) (e := e_b) hev hsn_e hsn_indep
  -- The old rows vanish at `update 0 v x` (their `Gᵥ`-edges avoid `v`).
  have hold : ∀ (j : so) (x : ScrewSpace k),
      FG.panelRow ends (j : β × _ × _)
        (Function.update (0 : α → ScrewSpace k) v x) = 0 := by
    rintro ⟨i, hi⟩ x
    have hlink := hso_link _ hi
    have h₁ : (ends i.1).1 ≠ v := fun h => hvVc (h ▸ hlink.left_mem)
    have h₂ : (ends i.1).2 ≠ v := fun h => hvVc (h ▸ hlink.right_mem)
    rw [BodyHingeFramework.panelRow, BodyHingeFramework.hingeRow_apply,
      Function.update_of_ne h₁, Function.update_of_ne h₂, Pi.zero_apply, Pi.zero_apply, sub_zero,
      map_zero]
  -- No `so`-index uses the new edge `e_b`: else `e_b` would be a `Gᵥ`-edge with endpoint `v`.
  have hso_ne_eb : ∀ i ∈ so, (i : β × _ × _).1 ≠ e_b := by
    intro i hi heq
    have hl := hso_link i hi
    rw [heq, hends_eb] at hl
    exact hvVc hl.left_mem
  -- The old-block count `Nat.card so = D(|V(Gv)|−1)` (the `_linking` producer's count, with
  -- `V(FGv.graph) = V(Gv)` definitionally).
  have hgraph : V((PanelHingeFramework.ofNormals Gv ends q₀).toBodyHinge.graph) = V(Gv) := rfl
  rw [hgraph] at hso_card
  -- `hnewpin` is stated through `(ends e_b).1`; rewrite it to `v`.
  rw [hends_eb] at hnewpin
  exact ⟨hane, hnewne, so, hso_card, hso_indep_G, hold, hso_ne_eb, sn, hsn_e, hsn_card, hsn_indep,
    hnewpin⟩

/-- **The eq. (6.12) candidate `t`-family** (KT's `p₁` at shear `t`, hinge-level and
role-parametric; Katoh–Tanigawa 2011 §6.4.1, Phase 22h). The candidate framework the W6
certify-then-rebase route varies over: it starts from the seed framework
`(ofNormals G ends q).toBodyHinge` and overrides two
hinge slots — the **candidate** hinge `e_c` (the free `va`-line `L = n_u ∧ n'`) gets support
`panelSupportExtensor n_u n'`, and the **reproduced** hinge `e_r` (KT's `p₁(vb) = q(ab)` at `t = 0`)
gets the sheared support `panelSupportExtensor (n_u + t • n') n_r`. All other hinges keep their seed
extensor. The roles instantiate as M₁ (`e_c := e_a, e_r := e_b, n_u := n_a, n_r := n_b`), M₂
(swap `a ↔ b`), M₃ (the relabeled seed). `F₀ := caseIIICandidate … 0` is the `t = 0` point: there
`e_r ↦ panelSupportExtensor n_u n_r`, which for M₁ is the `e₀`-meet `C(e₀)` exactly (reproduction).
Defined directly as a `BodyHingeFramework` (overriding `supportExtensor`) rather than through a
panel framework, because the candidate's two overridden hinges are not normal-assignments of a
single panel coordinatization — only the `e_r`-slot moves with `t`, linearly
(`caseIIICandidate_panelRow_eq_add_smul`, the W6f polynomiality input). -/
noncomputable def PanelHingeFramework.caseIIICandidate [DecidableEq β]
    (G : Graph α β) (ends : β → α × α) (q : α × Fin (k + 2) → ℝ)
    (e_c e_r : β) (n_u n' n_r : Fin (k + 2) → ℝ) (t : ℝ) :
    BodyHingeFramework k α β where
  graph := G
  supportExtensor := Function.update (Function.update
      ((PanelHingeFramework.ofNormals G ends q).toBodyHinge.supportExtensor)
      e_c (panelSupportExtensor n_u n'))
    e_r (panelSupportExtensor (n_u + t • n') n_r)

@[simp]
theorem PanelHingeFramework.caseIIICandidate_graph [DecidableEq β]
    (G : Graph α β) (ends : β → α × α) (q : α × Fin (k + 2) → ℝ)
    (e_c e_r : β) (n_u n' n_r : Fin (k + 2) → ℝ) (t : ℝ) :
    (PanelHingeFramework.caseIIICandidate G ends q e_c e_r n_u n' n_r t).graph = G := rfl

/-- **The candidate hinge's support is the `va`-line meet** (KT eq. (6.12); Phase 22h): at the
candidate hinge `e_c` (distinct from the reproduced hinge `e_r`), the `t`-family's supporting
extensor is `panelSupportExtensor n_u n'`, the panel-meet of the free `va`-line `L = n_u ∧ n'`,
independent of `t`. -/
theorem PanelHingeFramework.caseIIICandidate_supportExtensor_candidate [DecidableEq β]
    (G : Graph α β) (ends : β → α × α) (q : α × Fin (k + 2) → ℝ)
    {e_c e_r : β} (n_u n' n_r : Fin (k + 2) → ℝ) (t : ℝ) (hcr : e_c ≠ e_r) :
    (PanelHingeFramework.caseIIICandidate G ends q e_c e_r n_u n' n_r t).supportExtensor e_c
      = panelSupportExtensor n_u n' := by
  change Function.update (Function.update _ e_c _) e_r _ e_c = _
  rw [Function.update_of_ne hcr, Function.update_self]

/-- **The reproduced hinge's support is the sheared meet** (KT eq. (6.12), the `e_r`-slot;
Phase 22h): at the reproduced hinge `e_r`, the `t`-family's supporting extensor is
`panelSupportExtensor (n_u + t • n') n_r`. At `t = 0` it is `panelSupportExtensor n_u n_r` (for M₁,
`C(e₀)`), and it is the *only* slot moving with `t`. -/
theorem PanelHingeFramework.caseIIICandidate_supportExtensor_reproduced [DecidableEq β]
    (G : Graph α β) (ends : β → α × α) (q : α × Fin (k + 2) → ℝ)
    (e_c e_r : β) (n_u n' n_r : Fin (k + 2) → ℝ) (t : ℝ) :
    (PanelHingeFramework.caseIIICandidate G ends q e_c e_r n_u n' n_r t).supportExtensor e_r
      = panelSupportExtensor (n_u + t • n') n_r := by
  change Function.update (Function.update _ e_c _) e_r _ e_r = _
  rw [Function.update_self]

/-- **Every other hinge keeps the seed extensor** (KT eq. (6.12); Phase 22h): at a hinge `e`
distinct from both overridden slots `e_c`, `e_r`, the `t`-family's supporting extensor is the seed
framework's, independent of `t`, `n_u`, `n'`, `n_r`. -/
theorem PanelHingeFramework.caseIIICandidate_supportExtensor_of_ne [DecidableEq β]
    (G : Graph α β) (ends : β → α × α) (q : α × Fin (k + 2) → ℝ)
    (e_c e_r : β) (n_u n' n_r : Fin (k + 2) → ℝ) (t : ℝ) {e : β} (h1 : e ≠ e_c) (h2 : e ≠ e_r) :
    (PanelHingeFramework.caseIIICandidate G ends q e_c e_r n_u n' n_r t).supportExtensor e
      = (PanelHingeFramework.ofNormals G ends q).toBodyHinge.supportExtensor e := by
  change Function.update (Function.update _ e_c _) e_r _ e = _
  rw [Function.update_of_ne h2, Function.update_of_ne h1]

/-- **The candidate's panel rows are affine in the shear `t`** (the W6f one-variable transfer input;
Katoh–Tanigawa 2011 §6.4.1, eqs. (6.26)–(6.28), Phase 22h). Every panel row of the `t`-family
decomposes as its `t = 0` value plus a `t`-multiple of a fixed row, supported only on the reproduced
hinge `e_r`: the only `t`-dependence is the `e_r`-slot's supporting extensor
`panelSupportExtensor (n_u + t • n') n_r`, which splits as `panelSupportExtensor n_u n_r +
t • panelSupportExtensor n' n_r` (`panelSupportExtensor_add_left`/`_smul_left`), and `annihRow` is
linear in the extensor (`annihRow_add`/`_smul`), `hingeRow` linear in its block functional. So the
row at index `p = (e, t₁, t₂)` is `panelRow … 0 p + t • (if e = e_r then
hingeRow (ends e_r).1 (ends e_r).2 (annihRow (panelSupportExtensor n' n_r) t₁ t₂) else 0)`. This is
the precise polynomiality KT's Lemma 5.2 rank-transfer (W3) consumes to push the `F₀`-certified rank
along the family to a good `t`. -/
theorem PanelHingeFramework.caseIIICandidate_panelRow_eq_add_smul [DecidableEq β]
    (G : Graph α β) (ends : β → α × α) (q : α × Fin (k + 2) → ℝ)
    {e_c e_r : β} (n_u n' n_r : Fin (k + 2) → ℝ) (hcr : e_c ≠ e_r) (t : ℝ)
    (p : β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k) :
    (PanelHingeFramework.caseIIICandidate G ends q e_c e_r n_u n' n_r t).panelRow ends p
      = (PanelHingeFramework.caseIIICandidate G ends q e_c e_r n_u n' n_r 0).panelRow ends p
        + t • (if p.1 = e_r then BodyHingeFramework.hingeRow (ends e_r).1 (ends e_r).2
            (annihRow (panelSupportExtensor n' n_r) p.2.1 p.2.2) else 0) := by
  obtain ⟨e, t₁, t₂⟩ := p
  simp only [BodyHingeFramework.panelRow]
  rcases eq_or_ne e e_r with rfl | hne_r
  · -- The reproduced hinge: the extensor splits along the shear, carrying through `annihRow`/
    -- `hingeRow` linearity.
    rw [caseIIICandidate_supportExtensor_reproduced, caseIIICandidate_supportExtensor_reproduced,
      zero_smul, add_zero, panelSupportExtensor_add_left, panelSupportExtensor_smul_left,
      annihRow_add, annihRow_smul, BodyHingeFramework.hingeRow_eq_dualMap,
      BodyHingeFramework.hingeRow_eq_dualMap, BodyHingeFramework.hingeRow_eq_dualMap, map_add,
      map_smul, if_pos rfl]
  · -- Any other hinge: the extensor is `t`-independent, so the `t`-row equals the `t = 0` row.
    rcases eq_or_ne e e_c with rfl | hne_c
    · rw [caseIIICandidate_supportExtensor_candidate _ _ _ _ _ _ _ hcr,
        caseIIICandidate_supportExtensor_candidate _ _ _ _ _ _ _ hcr,
        if_neg hne_r, smul_zero, add_zero]
    · rw [caseIIICandidate_supportExtensor_of_ne _ _ _ _ _ _ _ _ _ hne_c hne_r,
        caseIIICandidate_supportExtensor_of_ne _ _ _ _ _ _ _ _ _ hne_c hne_r,
        if_neg hne_r, smul_zero, add_zero]

/-- **The one-variable rank transfer at the `t`-family** (W6f, the W3 KT-Lemma-5.2 transfer brick
specialized to `caseIIICandidate`; Katoh–Tanigawa 2011 §6.4.1, the certify-then-rebase step of
design §1.51(a)/(g); Phase 22h). Given a panel-row subfamily of the `t = 0` framework `F₀` (indexed
by `idx`) that is linearly independent at `t = 0` (`h0`) and any prescribed finite `bad` set of
shears, there is a *nonzero* `t` outside `bad` keeping the family linearly independent at `t`.

The `t`-rows are affine in `t` (`caseIIICandidate_panelRow_eq_add_smul`, W6a):
`g t i = A i + t • B i` with `A i := g 0 i` the `t = 0` rows and `B i` the `e_r`-correction. Picking
a finite basis `b` of the (finite-dimensional) dual `α → ScrewSpace k`, each coordinate
`b.repr (g t i) j = b.repr (A i) j + t * b.repr (B i) j` is the evaluation at `t` of the
degree-`≤ 1` polynomial `P i j := C (b.repr (A i) j) + X * C (b.repr (B i) j)`, so W3
(`LinearIndependent.exists_notMem_of_polynomial_repr`) supplies the good `t`. This is KT's "each
minor of `R(G, p_t)` is continuous in `t`" (pp. 668–669) in one-variable polynomial form. -/
theorem PanelHingeFramework.caseIIICandidate_exists_good_shear [DecidableEq β] [Finite α]
    (G : Graph α β) (ends : β → α × α) (q : α × Fin (k + 2) → ℝ)
    {e_c e_r : β} (hcr : e_c ≠ e_r) (n_u n' n_r : Fin (k + 2) → ℝ)
    {ι : Type*} [Finite ι]
    (idx : ι → β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k)
    (h0 : LinearIndependent ℝ (fun i => (PanelHingeFramework.caseIIICandidate G ends q
      e_c e_r n_u n' n_r 0).panelRow ends (idx i)))
    (bad : Finset ℝ) :
    ∃ t : ℝ, t ∉ bad ∧ t ≠ 0 ∧ LinearIndependent ℝ (fun i =>
      (PanelHingeFramework.caseIIICandidate G ends q e_c e_r n_u n' n_r t).panelRow
        ends (idx i)) := by
  classical
  -- The `t`-row family and its `t = 0` value / `e_r`-correction (the affine split of W6a).
  set g : ℝ → ι → Module.Dual ℝ (α → ScrewSpace k) := fun t i =>
    (PanelHingeFramework.caseIIICandidate G ends q e_c e_r n_u n' n_r t).panelRow ends (idx i)
    with hg_def
  set A : ι → Module.Dual ℝ (α → ScrewSpace k) := g 0 with hA_def
  set B : ι → Module.Dual ℝ (α → ScrewSpace k) := fun i =>
    if (idx i).1 = e_r then BodyHingeFramework.hingeRow (ends e_r).1 (ends e_r).2
      (annihRow (panelSupportExtensor n' n_r) (idx i).2.1 (idx i).2.2) else 0 with hB_def
  have hsplit : ∀ t i, g t i = A i + t • B i := fun t i => by
    rw [hg_def, hA_def, hB_def]
    exact caseIIICandidate_panelRow_eq_add_smul G ends q n_u n' n_r hcr t (idx i)
  -- A finite basis of the finite-dimensional dual, and the degree-`≤ 1` coordinate polynomials.
  let b := Module.finBasis ℝ (Module.Dual ℝ (α → ScrewSpace k))
  let P : ι → Fin (Module.finrank ℝ (Module.Dual ℝ (α → ScrewSpace k))) → Polynomial ℝ :=
    fun i j => Polynomial.C (b.repr (A i) j) + Polynomial.X * Polynomial.C (b.repr (B i) j)
  have hP : ∀ t i j, b.repr (g t i) j = (P i j).eval t := fun t i j => by
    rw [hsplit, map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
    simp only [P, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_X]
  obtain ⟨t, ht_bad, ht_ne, ht_li⟩ :=
    LinearIndependent.exists_notMem_of_polynomial_repr b g P hP h0 bad
  exact ⟨t, ht_bad, ht_ne, ht_li⟩

/-- **L2b-place (seed-from-line) — the inductive old/new blocks of the *line-indexed* candidate
placement** (`lem:case-III-claim612-line-in-panel-union`, the producer-direction generalization of
`case_III_old_new_blocks`; Katoh–Tanigawa 2011 §6.4.1, eqs. (6.12)/(6.45), Phase 22g). Where
`case_III_old_new_blocks` shears body `v`'s normal along the *fixed* IH `b`-normal `n_b`
(reproducing the `ab`-row, so the candidate's `va`-line is the *single* fixed panel-meet
`C(e₀) = n_a ∧ n_b ⊂ Π(a)`), this leaf shears along an **arbitrary** second normal `n'` of the
witness panel `Π(a)`: it places `v`'s normal at `n_a + t·n'` (`t ≠ 0`, `n_a = q(a,·)`), so the
candidate's `va`-hinge `e_a` is the line `L = n_a ∧ n' ⊂ Π(a)` (`panelSupportExtensor_add_smul_left`
makes `e_a`'s support `(-t)·panelSupportExtensor n_a n'`, the witness line `L`'s panel-meet up to
the harmless `-t` factor). This is the line-variation KT's eq. (6.12) "for any `L ⊂ Π(a)`" actually
ranges over — the single fixed-`n_b` shear of `case_III_old_new_blocks` is one point of it
(`n' = n_b`), and the existential restate of Claim 6.12 (`case_III_claim612`, §1.39) needs *every*
such line so the six joins (which span `⋀² ℝ⁴` by Lemma 2.1) are all reachable. The `-t` factor
cancels under the row-space criterion's `r`, so the Leaf-2b core
(`panelSupportExtensor_add_smul_left_ne_zero_of_join_ne_zero`) turns the existential witness
`r̂(p̄ᵢ ∨ p̄ⱼ) ≠ 0` for the points `pᵢ, pⱼ ∈ L` into the nonzero-row input
`r̂(F.supportExtensor e_a) ≠ 0` the criterion (`linearIndependent_sumElim_candidateRow_iff`) feeds
to the candidate-completion assembly.

The two transversality facts now enter as explicit hypotheses (the line `L` is genuine, and the
reproduced `vb`-hinge is transversal at the chosen `n'`/`t`): `hL : LinearIndependent ![n_a, n']`
gives the `va`-line nondegeneracy (`hane`), and `hnewtrans : LinearIndependent ![n_a + t·n', n_b]`
gives the `vb`-hinge transversal (`hnewne`) — the latter is the genericity-in-`t` condition the
producer must additionally supply (for the fixed-`n_b` case `case_III_old_new_blocks` derives both
from `hgab` alone via `panelSupportExtensor_add_smul_right`'s row reproduction, which only holds at
`n' = n_b`). Everything else — the OLD block, its vanishing through `v`'s column, the NEW block's
independence through `v`'s screw column — is the verbatim
`case_III_old_new_blocks` argument (it never reads body `v`'s normal value). -/
theorem PanelHingeFramework.case_III_old_new_blocks_of_line [DecidableEq α] [Finite α] [Finite β]
    (G Gv : Graph α β) (ends : β → α × α)
    {v a b : α} {e_a e_b : β} (hvVc : v ∉ V(Gv)) (haVc : a ∈ V(Gv)) (hbVc : b ∈ V(Gv))
    (_hG_eb : G.IsLink e_b v b) (hends_eb : ends e_b = (v, b))
    (_hG_ea : G.IsLink e_a v a) (hends_ea : ends e_a = (v, a))
    {q : α × Fin (k + 2) → ℝ}
    (hends_Gv : ∀ e u w, Gv.IsLink e u w → Gv.IsLink e (ends e).1 (ends e).2)
    (hne_Gv : ∀ e, Gv.IsLink e (ends e).1 (ends e).2 →
      (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge.supportExtensor e ≠ 0)
    (hrig : (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge.IsInfinitesimallyRigidOn V(Gv))
    {t : ℝ} (ht : t ≠ 0)
    -- the witness panel's second normal `n'` (the `va`-line `L = n_a ∧ n'`) and the eq. (6.12)
    -- line-indexed seed `q₀` shearing body `v` along `n'` (not the fixed IH `n_b`)
    (n' : Fin (k + 2) → ℝ)
    (q₀ : α × Fin (k + 2) → ℝ)
    (hq₀ : q₀ = fun p => if p.1 = v then
        ((fun i => q (a, i)) + t • n') p.2 else q p)
    -- the `va`-line `L ⊂ Π(a)` is genuine, and the reproduced `vb`-hinge is transversal at `t`/`n'`
    (hL : LinearIndependent ℝ ![(fun i => q (a, i)), n'])
    (hnewtrans :
      LinearIndependent ℝ ![((fun i => q (a, i)) + t • n'), (fun i => q (b, i))]) :
    -- `v`'s `a`-hinge nondegeneracy (the `va`-line `L ⊂ Π(a)`, KT eq. (6.12), `t ≠ 0`) and the
    -- reproduced `vb`-hinge transversal (the new block sits on it).
    (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.supportExtensor e_a ≠ 0 ∧
    (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.supportExtensor e_b ≠ 0 ∧
    -- the OLD block `so`: `D(|V(Gv)|−1)` independent linking rows, vanishing at `v`'s column.
    ∃ so : Set (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k),
      Nat.card so = screwDim k * (V(Gv).ncard - 1) ∧
      LinearIndependent ℝ (fun i : so =>
        (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.panelRow ends (i : β × _ × _)) ∧
      (∀ (j : so) (x : ScrewSpace k),
        (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.panelRow ends (j : β × _ × _)
          (Function.update (0 : α → ScrewSpace k) v x) = 0) ∧
      (∀ i ∈ so, (i : β × _ × _).1 ≠ e_b) ∧
    -- the NEW block `sn`: the `D − 1` independent `e_b`-rows, staying independent through `v`'s
    -- column (`hnewpin`).
    ∃ sn : Set (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k),
      (∀ i ∈ sn, (i : β × _ × _).1 = e_b) ∧ Nat.card sn = screwDim k - 1 ∧
      LinearIndependent ℝ (fun i : sn =>
        (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.panelRow ends (i : β × _ × _)) ∧
      LinearIndependent ℝ (fun i : sn =>
        ((PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.panelRow ends
          (i : β × _ × _)).comp
          (LinearMap.single ℝ (fun _ : α => ScrewSpace k) v)) := by
  classical
  haveI : Fintype α := Fintype.ofFinite α
  set FG := (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge with hFG
  set n_a : Fin (k + 2) → ℝ := fun i => q (a, i) with hn_a
  set n_b : Fin (k + 2) → ℝ := fun i => q (b, i) with hn_b
  -- (1) The shared seed is the IH seed with `v`'s normal overridden by `n_a + t • n'`, so the IH
  -- rigidity transports to `q₀` (overriding the fresh `v ∉ V(Gᵥ)` leaves the `Gᵥ`-block untouched).
  have hqeq : (fun p => if p.1 = v then ((n_a + t • n') : Fin (k + 2) → ℝ) p.2 else q p) = q₀ := by
    rw [hq₀]
  have hwN : PanelHingeFramework.ofNormals Gv ends q₀
      = (PanelHingeFramework.ofNormals Gv ends q).withNormal v (n_a + t • n') := by
    rw [← hqeq]
    exact PanelHingeFramework.ofNormals_update_eq_withNormal Gv ends q v (n_a + t • n')
  -- No `Gᵥ`-edge touches `v` (its endpoints lie in `V(Gᵥ)`, and `v ∉ V(Gᵥ)`).
  have hvedge : ∀ e u w, Gv.IsLink e u w → (ends e).1 ≠ v ∧ (ends e).2 ≠ v := by
    intro e u w he
    have hl := hends_Gv e u w he
    exact ⟨fun h => hvVc (h ▸ hl.left_mem), fun h => hvVc (h ▸ hl.right_mem)⟩
  -- The motion space is unchanged when overriding the unhinged `v`, so the IH rigidity transports.
  have hZeq : (PanelHingeFramework.ofNormals Gv ends q₀).toBodyHinge.infinitesimalMotions
      = (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge.infinitesimalMotions := by
    rw [hwN]
    exact (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge_withNormal_infinitesimalMotions_eq
      v (n_a + t • n') hvedge
  have hrig₀ :
      (PanelHingeFramework.ofNormals Gv ends q₀).toBodyHinge.IsInfinitesimallyRigidOn V(Gv) := by
    intro S hS u hu w hw
    refine hrig S ?_ u hu w hw
    rw [← BodyHingeFramework.mem_infinitesimalMotions, ← hZeq,
      BodyHingeFramework.mem_infinitesimalMotions] at *
    exact hS
  -- The `Gᵥ`-hinges stay transversal at `q₀` (endpoints avoid `v`, where `q₀` agrees with `q`).
  have hne₀ : ∀ e, Gv.IsLink e (ends e).1 (ends e).2 →
      (PanelHingeFramework.ofNormals Gv ends q₀).toBodyHinge.supportExtensor e ≠ 0 := by
    intro e he
    obtain ⟨h₁, h₂⟩ := hvedge e _ _ he
    rw [hwN, (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge_withNormal_supportExtensor_of_ne
      v (n_a + t • n') e (by simpa using h₁) (by simpa using h₂)]
    exact hne_Gv e he
  -- (2) OLD block (N7b-0, `_linking`): the rigid `Gᵥ`-realization carries `D(|V(Gᵥ)|−1)`
  -- independent linking panel rows of `ofNormals Gv ends q₀`.
  have hVGvne : V(Gv).Nonempty := ⟨b, hbVc⟩
  set FGv := (PanelHingeFramework.ofNormals Gv ends q₀).toBodyHinge with hFGv
  obtain ⟨so, hso_link, hso_card, hso_indep⟩ :=
    FGv.exists_independent_panelRow_subfamily_of_rigidOn_linking (ends := ends)
      (by simpa [hFGv] using hends_Gv) (by simpa [hFGv] using hne₀) (by simpa [hFGv] using hVGvne)
      (by simpa [hFGv] using hrig₀)
  -- (3) Transport the old block onto `G` (N7b-2; `panelRow` reads only `ends`/`q₀`, not the graph,
  -- so `hrow := rfl`).
  have hso_indep_G : LinearIndependent ℝ (fun i : so =>
      FG.panelRow ends (i : β × _ × _)) :=
    PanelHingeFramework.exists_independent_panelRow_transport Gv G ends ends q₀ q₀
      (f := id) Function.injective_id (fun i => rfl) hso_indep
  -- The re-inserted body `v` and its neighbour `b` are distinct (`b ∈ V(Gᵥ)`, `v ∉ V(Gᵥ)`).
  have hvb : v ≠ b := fun h => hvVc (h ▸ hbVc)
  -- The line-indexed seed reads `q₀(v,·) = n_a + t·n'` and `q₀(b,·) = n_b`.
  have hq₀v : (fun i => q₀ (v, i)) = n_a + t • n' := by
    funext i; rw [hq₀]; simp
  have hq₀b : (fun i => q₀ (b, i)) = n_b := by
    funext i; rw [hq₀, hn_b]; simp only [if_neg hvb.symm]
  have hva : v ≠ a := fun h => hvVc (h ▸ haVc)
  have hq₀a : (fun i => q₀ (a, i)) = n_a := by
    funext i; rw [hq₀, hn_a]; simp only [if_neg hva.symm]
  -- The `va`-hinge `e_a` is the line `L = n_a ∧ n' ⊂ Π(a)` (KT eq. (6.12), `t ≠ 0`): its support is
  -- `(-t) · panelSupportExtensor n_a n'`, nonzero since `![n_a, n']` is independent.
  have hane : FG.supportExtensor e_a ≠ 0 := by
    rw [PanelHingeFramework.toBodyHinge_supportExtensor, PanelHingeFramework.ofNormals_ends,
      PanelHingeFramework.ofNormals_normal, PanelHingeFramework.ofNormals_normal, hends_ea]
    simp only [hq₀v, hq₀a, panelSupportExtensor_add_smul_left]
    exact smul_ne_zero (neg_ne_zero.mpr ht) ((panelSupportExtensor_ne_zero_iff n_a n').mpr hL)
  -- (4) NEW block (N7b-1): the reproduced `vb`-hinge `e_b` is transversal at the chosen `n'`/`t`
  -- (`hnewtrans : ![n_a + t·n', n_b]` independent), giving `D − 1` independent new rows.
  have hnewne : FG.supportExtensor e_b ≠ 0 := by
    rw [PanelHingeFramework.toBodyHinge_supportExtensor, PanelHingeFramework.ofNormals_ends,
      PanelHingeFramework.ofNormals_normal, PanelHingeFramework.ofNormals_normal, hends_eb]
    simp only [hq₀v, hq₀b]
    exact (panelSupportExtensor_ne_zero_iff (n_a + t • n') n_b).mpr hnewtrans
  have hev : (ends e_b).2 ≠ (ends e_b).1 := by rw [hends_eb]; exact hvb.symm
  obtain ⟨sn, hsn_e, hsn_card, hsn_indep⟩ :=
    FG.exists_independent_panelRow_subfamily_of_edge
      (ends := ends) (e := e_b) (by rw [hends_eb]; exact hvb) hnewne
  -- `hnewpin`: the new rows stay independent through `v = (ends e_b).1`'s screw column.
  have hnewpin := FG.linearIndependent_panelRow_comp_single_of_edge
    (ends := ends) (e := e_b) hev hsn_e hsn_indep
  -- The old rows vanish at `update 0 v x` (their `Gᵥ`-edges avoid `v`).
  have hold : ∀ (j : so) (x : ScrewSpace k),
      FG.panelRow ends (j : β × _ × _)
        (Function.update (0 : α → ScrewSpace k) v x) = 0 := by
    rintro ⟨i, hi⟩ x
    have hlink := hso_link _ hi
    have h₁ : (ends i.1).1 ≠ v := fun h => hvVc (h ▸ hlink.left_mem)
    have h₂ : (ends i.1).2 ≠ v := fun h => hvVc (h ▸ hlink.right_mem)
    rw [BodyHingeFramework.panelRow, BodyHingeFramework.hingeRow_apply,
      Function.update_of_ne h₁, Function.update_of_ne h₂, Pi.zero_apply, Pi.zero_apply, sub_zero,
      map_zero]
  -- No `so`-index uses the new edge `e_b`: else `e_b` would be a `Gᵥ`-edge with endpoint `v`.
  have hso_ne_eb : ∀ i ∈ so, (i : β × _ × _).1 ≠ e_b := by
    intro i hi heq
    have hl := hso_link i hi
    rw [heq, hends_eb] at hl
    exact hvVc hl.left_mem
  -- The old-block count `Nat.card so = D(|V(Gv)|−1)` (the `_linking` producer's count, with
  -- `V(FGv.graph) = V(Gv)` definitionally).
  have hgraph : V((PanelHingeFramework.ofNormals Gv ends q₀).toBodyHinge.graph) = V(Gv) := rfl
  rw [hgraph] at hso_card
  -- `hnewpin` is stated through `(ends e_b).1`; rewrite it to `v`.
  rw [hends_eb] at hnewpin
  exact ⟨hane, hnewne, so, hso_card, hso_indep_G, hold, hso_ne_eb, sn, hsn_e, hsn_card, hsn_indep,
    hnewpin⟩

/-- **L2b-place (per-line criterion) — the line-indexed candidate placement attains the full
`D(|V|−1)` family when the common vector is not orthogonal to the witness line's panel-meet**
(`lem:case-III-claim612-line-in-panel-union`, the row-space-criterion leaf of the `d = 3` `hsplit`
producer; Katoh–Tanigawa 2011 §6.4.1, eqs.~(6.12)/(6.29)/(6.42), Phase 22g). With the line-indexed
OLD/NEW block placement in hand (`case_III_old_new_blocks_of_line`, whose `va`-hinge `e_a` is the
witness line `L = n_a ∧ n' ⊂ Π(a)`, support `(-t)·C(L)`), this leaf runs KT's eq.~(6.42) row-space
criterion (`linearIndependent_sumElim_candidateRow_iff`) **at `e_a`** to append the candidate `+1`
row `hingeRow v a r̂` and lift the eq.~(6.12) `D(|V|−1)−1` brick to the full `D(|V|−1)` family.

The structure is the `M₁` candidate-completion
(`linearIndependent_sum_augment_candidateRow_selector`, split off at `v` along the *original* edge
`va = e_a`): the **NEW block** `rn` is the `D − 1` panel rows of the `va`-hinge `e_a` itself
(`exists_independent_panelRow_subfamily_of_edge` at `e_a`), pinned to `v`'s screw column
(`linearIndependent_panelRow_comp_single_of_edge`) and spanning the whole hinge block
`r(p(e_a)) = (span C(e_a))^⊥` (`span_panelRow_comp_single_of_edge`, L2); the selector's operated
forms `(rn ·) ∘ₗ Φ ∘ₗ single v` (`Φ = columnOp hva`) reduce to those bare pinned forms by
`comp_columnOp_comp_single` (the column op is the identity on `v`'s column). The OLD block `ro`
(the `D(|V(Gv)|−1)` linking rows, vanishing at `v`'s column — `hold`/`holdindep`) is carried in. The
criterion then fires on the **witness input** `r̂(C(e_a)) ≠ 0` (`hr`), which the Leaf-2b geometric
core `panelSupportExtensor_add_smul_left_ne_zero_of_join_ne_zero` supplies from Claim~6.12's
existential join witness `r̂(p̄ᵢ ∨ p̄ⱼ) ≠ 0` — so the full
`Sum.elim (Sum.elim rn {hingeRow v a r̂}) ro` family is linearly independent, the eq.~(6.29)
candidate family the fixed-placement device feed (C2) consumes.

Graph-free over the abstract `F` (it reads only `ends`/`supportExtensor`/`panelRow`/`hingeRow`); the
recurring `ofNormals`/`withGraph` defeq trap (TACTICS-QUIRKS §38) is confined to the producer's seed
feed (Leaf 3), which supplies `hane`/`hold`/`holdindep` at the concrete carrier. -/
theorem PanelHingeFramework.case_III_full_family_of_line [DecidableEq α]
    (F : BodyHingeFramework k α β) (ends : β → α × α)
    {v a : α} {e_a : β} (hva : v ≠ a) (hends_ea : ends e_a = (v, a))
    (hane : F.supportExtensor e_a ≠ 0)
    {ιo : Type*} [Finite ιo] {ro : ιo → Module.Dual ℝ (α → ScrewSpace k)}
    (hold : ∀ (j : ιo) (x : ScrewSpace k), ro j (Function.update (0 : α → ScrewSpace k) v x) = 0)
    (holdindep : LinearIndependent ℝ ro)
    (r : Module.Dual ℝ (ScrewSpace k)) (hr : r (F.supportExtensor e_a) ≠ 0) :
    ∃ sn : Set (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k),
      (∀ i ∈ sn, (i : β × _ × _).1 = e_a) ∧ Nat.card sn = screwDim k - 1 ∧
      LinearIndependent ℝ
        (Sum.elim
          (Sum.elim (fun i : sn => F.panelRow ends (i : β × _ × _))
            (fun _ : Unit => BodyHingeFramework.hingeRow (k := k) (α := α) v a r))
          ro) := by
  -- The `va`-hinge `e_a` is transversal (`(ends e_a).1 = v ≠ a = (ends e_a).2`).
  have huv : (ends e_a).1 ≠ (ends e_a).2 := by rw [hends_ea]; exact hva
  have hev : (ends e_a).2 ≠ (ends e_a).1 := huv.symm
  -- The `va`-hinge first endpoint is `v`.
  have h1v : (ends e_a).1 = v := by rw [hends_ea]
  -- (NEW block) the `D − 1` panel rows of the `va`-hinge `e_a`.
  obtain ⟨sn, hsn_e, hsn_card, hsn_indep⟩ :=
    F.exists_independent_panelRow_subfamily_of_edge (ends := ends) (e := e_a) huv hane
  refine ⟨sn, hsn_e, hsn_card, ?_⟩
  -- The pinned NEW-block rows are independent (`linearIndependent_panelRow_comp_single_of_edge`,
  -- bare `single v` form) and span the whole hinge block (`span_panelRow_comp_single_of_edge`, L2).
  have hpin := F.linearIndependent_panelRow_comp_single_of_edge (ends := ends) (e := e_a)
    hev hsn_e hsn_indep
  haveI : Finite ↥sn := hpin.finite
  have hspan := F.span_panelRow_comp_single_of_edge (ends := ends) (e := e_a)
    hev hane hsn_e hsn_card hsn_indep
  rw [h1v] at hpin hspan
  -- Reroute the bare `single v` forms into the selector's operated `Φ ∘ single v` forms
  -- (`comp_columnOp_comp_single`: the column op is the identity on `v`'s screw column).
  have hbridge : (fun i : sn => ((F.panelRow ends (i : β × _ × _)).comp
        (BodyHingeFramework.columnOp (k := k) hva).toLinearMap).comp
        (LinearMap.single ℝ (fun _ : α => ScrewSpace k) v))
      = (fun i : sn => (F.panelRow ends (i : β × _ × _)).comp
        (LinearMap.single ℝ (fun _ : α => ScrewSpace k) v)) := by
    funext i; exact BodyHingeFramework.comp_columnOp_comp_single hva _
  have hrnpin : LinearIndependent ℝ (fun i : sn =>
      ((F.panelRow ends (i : β × _ × _)).comp
          (BodyHingeFramework.columnOp (k := k) hva).toLinearMap).comp
        (LinearMap.single ℝ (fun _ : α => ScrewSpace k) v)) := by
    rw [hbridge]; exact hpin
  have hspan' : Submodule.span ℝ (Set.range (fun i : sn =>
      ((F.panelRow ends (i : β × _ × _)).comp
          (BodyHingeFramework.columnOp (k := k) hva).toLinearMap).comp
        (LinearMap.single ℝ (fun _ : α => ScrewSpace k) v))) = F.hingeRowBlock e_a := by
    rw [hbridge]; exact hspan
  exact BodyHingeFramework.linearIndependent_sum_augment_candidateRow_selector
    F e_a hva hold holdindep hrnpin hspan' hr

/-- **W6c — the restriction-form full candidate family** (`lem:case-II-realization` /
`lem:case-III`, the restriction-bottom sibling of `case_III_full_family_of_line`; Katoh–Tanigawa
2011 §6.4.1, eqs.~(6.12)/(6.29), Phase 22h §1.51(d)). Builds the same NEW block as
`case_III_full_family_of_line` — the `D − 1` panel rows of the `va`-hinge `e_a`
(`exists_independent_panelRow_subfamily_of_edge`) pinned to `v`'s screw column and spanning the
whole hinge block, plus the candidate row `hingeRow v a r` appended via KT's eq.~(6.42) row-space
criterion (`linearIndependent_sumElim_candidateRow_iff` on the witness `r(C(e_a)) ≠ 0`, `hr`) — but
**closes against a restriction-independent bottom block** `ro` rather than the pure-`v`-vanishing
one. Where
`_of_line` consumes the `hold`/`holdindep` (pure-`v`-vanishing) old block through the
candidate-completion selector, this leaf consumes W4's restriction-independence contract
`hbotrestrict` (the `ro`-rows independent only after composing with the column op `Φ = columnOp hva`
and the off-`v` projection `P_v = id − single v ∘ₗ proj v`) through the W6-core augment
`linearIndependent_sum_augment_candidateRow_restriction`.

The two W6-core inputs are assembled from the same NEW-block data the `_of_line` body builds: the
operated, pinned top block `hnewpinaug` is the selector's inline `rw [hingeRow_comp_columnOp_comp_
single] ; (linearIndependent_sumElim_candidateRow_iff …).2 hr` two-liner verbatim, and the NEW-block
vanishing `hrnvanish` reads each `sn`-row as `hingeRow v a (annihRow (C(e_a)) …)` (the panel row of
the `va`-hinge `e_a` at `ends e_a = (v, a)`, by `panelRow_eq_hingeRow_annihRow_of_ends`) and applies
`hingeRow_comp_columnOp_vanish_off`. This is the `t = 0` candidate `F₀` certification's abstract
core (W6d feeds it the restriction-transported bottom). Graph-free over the abstract `F` (it reads
only `ends`/`supportExtensor`/`panelRow`/`hingeRow`); the `ofNormals`/`withGraph` defeq trap
(TACTICS-QUIRKS §38) is confined to the producer's seed feed. -/
theorem PanelHingeFramework.case_III_full_family_restriction [DecidableEq α]
    (F : BodyHingeFramework k α β) (ends : β → α × α)
    {v a : α} {e_a : β} (hva : v ≠ a) (hends_ea : ends e_a = (v, a))
    (hane : F.supportExtensor e_a ≠ 0)
    {ιo : Type*} [Finite ιo] {ro : ιo → Module.Dual ℝ (α → ScrewSpace k)}
    (hbotrestrict : LinearIndependent ℝ
      (fun j : ιo => ((ro j).comp (BodyHingeFramework.columnOp (k := k) hva).toLinearMap).comp
        ((LinearMap.id : (α → ScrewSpace k) →ₗ[ℝ] (α → ScrewSpace k))
          - (LinearMap.single ℝ (fun _ : α => ScrewSpace k) v).comp (LinearMap.proj v))))
    (r : Module.Dual ℝ (ScrewSpace k)) (hr : r (F.supportExtensor e_a) ≠ 0) :
    ∃ sn : Set (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k),
      (∀ i ∈ sn, (i : β × _ × _).1 = e_a) ∧ Nat.card sn = screwDim k - 1 ∧
      LinearIndependent ℝ
        (Sum.elim
          (Sum.elim (fun i : sn => F.panelRow ends (i : β × _ × _))
            (fun _ : Unit => BodyHingeFramework.hingeRow (k := k) (α := α) v a r))
          ro) := by
  -- The `va`-hinge `e_a` is transversal; its first endpoint is `v` (the same setup as `_of_line`).
  have huv : (ends e_a).1 ≠ (ends e_a).2 := by rw [hends_ea]; exact hva
  have hev : (ends e_a).2 ≠ (ends e_a).1 := huv.symm
  have h1v : (ends e_a).1 = v := by rw [hends_ea]
  -- (NEW block) the `D − 1` panel rows of the `va`-hinge `e_a`.
  obtain ⟨sn, hsn_e, hsn_card, hsn_indep⟩ :=
    F.exists_independent_panelRow_subfamily_of_edge (ends := ends) (e := e_a) huv hane
  refine ⟨sn, hsn_e, hsn_card, ?_⟩
  -- The pinned NEW-block rows are independent and span the whole hinge block.
  have hpin := F.linearIndependent_panelRow_comp_single_of_edge (ends := ends) (e := e_a)
    hev hsn_e hsn_indep
  haveI : Finite ↥sn := hpin.finite
  have hspan := F.span_panelRow_comp_single_of_edge (ends := ends) (e := e_a)
    hev hane hsn_e hsn_card hsn_indep
  rw [h1v] at hpin hspan
  -- Reroute the bare `single v` forms into the operated `Φ ∘ single v` forms.
  have hbridge : (fun i : sn => ((F.panelRow ends (i : β × _ × _)).comp
        (BodyHingeFramework.columnOp (k := k) hva).toLinearMap).comp
        (LinearMap.single ℝ (fun _ : α => ScrewSpace k) v))
      = (fun i : sn => (F.panelRow ends (i : β × _ × _)).comp
        (LinearMap.single ℝ (fun _ : α => ScrewSpace k) v)) := by
    funext i; exact BodyHingeFramework.comp_columnOp_comp_single hva _
  have hrnpin : LinearIndependent ℝ (fun i : sn =>
      ((F.panelRow ends (i : β × _ × _)).comp
          (BodyHingeFramework.columnOp (k := k) hva).toLinearMap).comp
        (LinearMap.single ℝ (fun _ : α => ScrewSpace k) v)) := by
    rw [hbridge]; exact hpin
  have hspan' : Submodule.span ℝ (Set.range (fun i : sn =>
      ((F.panelRow ends (i : β × _ × _)).comp
          (BodyHingeFramework.columnOp (k := k) hva).toLinearMap).comp
        (LinearMap.single ℝ (fun _ : α => ScrewSpace k) v))) = F.hingeRowBlock e_a := by
    rw [hbridge]; exact hspan
  -- (W6-core input 1) the operated, pinned top block is independent: the eq.~(6.42) row-space
  -- criterion fires on the witness `r(C(e_a)) ≠ 0` (the selector's inline `hnewpinaug` two-liner).
  have hnewpinaug : LinearIndependent ℝ (Sum.elim
      (fun i : sn =>
        ((F.panelRow ends (i : β × _ × _)).comp
          (BodyHingeFramework.columnOp (k := k) hva).toLinearMap).comp
          (LinearMap.single ℝ (fun _ : α => ScrewSpace k) v))
      (fun _ : Unit =>
        ((BodyHingeFramework.hingeRow (k := k) (α := α) v a r).comp
          (BodyHingeFramework.columnOp (k := k) hva).toLinearMap).comp
          (LinearMap.single ℝ (fun _ : α => ScrewSpace k) v))) := by
    rw [BodyHingeFramework.hingeRow_comp_columnOp_comp_single hva r]
    exact (BodyHingeFramework.linearIndependent_sumElim_candidateRow_iff F e_a hrnpin hspan' r).2
      hr
  -- (W6-core input 2) the NEW-block rows vanish off `v`'s column in the operated frame: each
  -- `sn`-row is `hingeRow v a (annihRow (C(e_a)) …)` (panel row of the `va`-hinge `e_a`), so
  -- `hingeRow_comp_columnOp_vanish_off` applies.
  have hrnvanish : ∀ (i : sn) (S : α → ScrewSpace k), S v = 0 →
      (F.panelRow ends (i : β × _ × _)).comp
        (BodyHingeFramework.columnOp (k := k) hva).toLinearMap S = 0 := by
    rintro ⟨⟨e', t₁, t₂⟩, hmem⟩ S hS
    have he' : e' = e_a := hsn_e _ hmem
    subst he'
    rw [LinearMap.comp_apply, LinearEquiv.coe_coe,
      F.panelRow_eq_hingeRow_annihRow_of_ends ends hends_ea t₁ t₂,
      BodyHingeFramework.hingeRow_comp_columnOp_vanish_off hva _ S hS]
  -- The W6-core augment fires (restriction-bottom in place of pure-`v`-vanishing).
  exact BodyHingeFramework.linearIndependent_sum_augment_candidateRow_restriction
    hva hrnvanish hnewpinaug hbotrestrict

/-- **W6d — the `t = 0` rank certification at `F₀`** (`lem:case-III`, the certify step of the
certify-then-rebase route; Katoh–Tanigawa 2011 §6.4.1, eq. (6.29), the certify half of design
§1.51(a)/(e); Phase 22h). The KT-(6.29) count at the `t = 0` candidate framework
`F₀ := caseIIICandidate G ends q e_a e_b n_a n' n_b 0` — concluded in the *consumable* form a rank
lower bound `D(|V(G)|−1) ≤ finrank (span ℝ F₀.rigidityRows)`. This is KT's own reading of (6.29)
("if the top-left `6×6` block is full rank then `rank R(G,p₁) = 6(|V|−1)`", p. 684 — a statement
about the *rank* of `R(G,p₁)`, not about a distinguished row family), the step that lets the rebase
(W6e) re-extract a literal `F₀.panelRow` family of that size for the W6f transfer.

The certified family is W6c's restriction-form `Sum.elim (Sum.elim (sn-rows) {hingeRow v a ρ}) w̃`
at `F := F₀`: the `D − 1` `e_a`-panel rows of the candidate hinge, the candidate row
`hingeRow v a ρ` (the redundant `ab`-combination W6b supplies as `ρ`), and a transported copy `w̃`
of W6b's `D(m_v−1)` bottom rows. The bottom transport (i) replaces each `w j` by a row `w̃ j` whose
`Φ ∘ P_v`-composite (`Φ = columnOp hva`, `P_v = id − single v ∘ proj v`, W4's off-`v` restriction)
is `w j` itself: a genuine `G_v`-row `hingeRow u w' r'` (`u, w' ≠ v` by `hvVc`) survives by brick 2
(`comp_columnOp_comp_offProj_of_single_eq_zero`, via `hingeRow_comp_single_off`), and a transported
`ρ'`-row enters as `hingeRow v b ρ'`, whose composite is `hingeRow a b ρ' = w j` (brick 1,
`hingeRow_comp_columnOp_comp_offProj`); so `hbotrestrict` holds by `hw`. (ii) W6c then certifies the
family LI at `F₀`. (iii) Every member lies in `span ℝ F₀.rigidityRows`: the `sn`-rows are genuine
`F₀`-rows of the candidate `e_a`-link; the candidate collapses by the eq.-(6.27) identity
`hingeRow v a ρ = hingeRow v b ρ − hingeRow a b ρ` (`hingeRow_sub_hingeRow_eq`) into a genuine
`e_b`-row `hingeRow v b ρ` (`ρ(C(e₀)) = 0` at `t = 0`, `hρe₀`) minus `hingeRow a b ρ`, a member of
`span F_v`-rows (`hρGv`) — and `span F_v`-rows `≤ span F₀`-rows since every `G_v`-edge keeps its
seed extensor; the
`w̃`-rows per-tag the same way. (iv) The family is `(sn ⊕ Unit) ⊕ ιb` of card
`((D−1)+1) + D(m_v−1) = D·m_v = D(|V(G)|−1)`, and `finrank_span_eq_card` + `Submodule.finrank_mono`
convert LI-in-span to the bound. -/
theorem PanelHingeFramework.case_III_rank_certification
    [DecidableEq β] [Finite α]
    (G Gv : Graph α β) (ends : β → α × α) {q : α × Fin (k + 2) → ℝ}
    {v a b : α} {e_a e_b : β}
    (hvVc : v ∉ V(Gv)) (haVc : a ∈ V(Gv)) (hbVc : b ∈ V(Gv))
    (hG_ea : G.IsLink e_a v a) (hG_eb : G.IsLink e_b v b)
    (hends_ea : ends e_a = (v, a)) (hends_eb : ends e_b = (v, b)) (heab : e_a ≠ e_b)
    (hleG : ∀ e u w, Gv.IsLink e u w → G.IsLink e u w)
    (hVone : 1 ≤ V(Gv).ncard) (hVcard : V(G).ncard = V(Gv).ncard + 1)
    {n' : Fin (k + 2) → ℝ}
    (hLn : LinearIndependent ℝ ![(fun i => q (a, i)), n'])
    {ρ : Module.Dual ℝ (ScrewSpace k)}
    (hρgate : ρ (panelSupportExtensor (fun i => q (a, i)) n') ≠ 0)
    (hρe₀ : ρ (panelSupportExtensor (fun i => q (a, i)) (fun i => q (b, i))) = 0)
    (hρGv : BodyHingeFramework.hingeRow a b ρ ∈ Submodule.span ℝ
      (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge.rigidityRows)
    {ιb : Type*} [Finite ιb] {w : ιb → Module.Dual ℝ (α → ScrewSpace k)}
    (hwcard : Nat.card ιb = screwDim k * (V(Gv).ncard - 1))
    (hw : LinearIndependent ℝ w)
    (hwmem : ∀ j, w j ∈ (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge.rigidityRows ∨
      ∃ ρ' : Module.Dual ℝ (ScrewSpace k),
        ρ' (panelSupportExtensor (fun i => q (a, i)) (fun i => q (b, i))) = 0 ∧
        w j = BodyHingeFramework.hingeRow a b ρ') :
    screwDim k * (V(G).ncard - 1)
      ≤ Module.finrank ℝ (Submodule.span ℝ
          (PanelHingeFramework.caseIIICandidate G ends q e_a e_b
            (fun i => q (a, i)) n' (fun i => q (b, i)) 0).rigidityRows) := by
  classical
  haveI : Fintype α := Fintype.ofFinite α
  haveI : Fintype ιb := Fintype.ofFinite ιb
  set na := (fun i => q (a, i)) with hna
  set nb := (fun i => q (b, i)) with hnb
  set F₀ := PanelHingeFramework.caseIIICandidate G ends q e_a e_b na n' nb 0 with hF₀
  set Fv := (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge with hFv
  have hva : v ≠ a := fun h => hvVc (h ▸ haVc)
  have hvb : v ≠ b := fun h => hvVc (h ▸ hbVc)
  -- The candidate hinge `e_a`'s support at `F₀` is the `va`-line meet `C(L) = panelSupportExtensor
  -- na n'`, nonzero (the free line is transversal, `hLn`); the gate `hρgate` reads on it.
  have hsuppea : F₀.supportExtensor e_a = panelSupportExtensor na n' :=
    PanelHingeFramework.caseIIICandidate_supportExtensor_candidate G ends q na n' nb 0 heab
  have hane : F₀.supportExtensor e_a ≠ 0 := by
    rw [hsuppea]; exact (panelSupportExtensor_ne_zero_iff na n').mpr hLn
  have hr : ρ (F₀.supportExtensor e_a) ≠ 0 := by rw [hsuppea]; exact hρgate
  -- The reproduced hinge `e_b`'s support at `t = 0` is `panelSupportExtensor na nb = C(e₀)`.
  have hsuppeb : F₀.supportExtensor e_b = panelSupportExtensor na nb := by
    rw [hF₀, PanelHingeFramework.caseIIICandidate_supportExtensor_reproduced, zero_smul, add_zero]
  -- `Φ = columnOp hva` (col_a += col_v); `P_v = id − single v ∘ proj v` (W4's off-`v` restriction).
  set Φ := BodyHingeFramework.columnOp (k := k) hva with hΦ
  set Pv : (α → ScrewSpace k) →ₗ[ℝ] (α → ScrewSpace k) :=
    (LinearMap.id : (α → ScrewSpace k) →ₗ[ℝ] (α → ScrewSpace k))
      - (LinearMap.single ℝ (fun _ : α => ScrewSpace k) v).comp (LinearMap.proj v) with hPv
  -- The seed off `{e_a, e_b}` agrees with `Fv` (graph-free `ofNormals` support).
  have hseed_eq : ∀ e, (PanelHingeFramework.ofNormals G ends q).toBodyHinge.supportExtensor e
      = Fv.supportExtensor e := fun _ => rfl
  -- A `G_v`-edge keeps its `F₀`-seed extensor: its endpoints are in `V(Gv)`, so neither is `v`,
  -- hence `e ≠ e_a` and `e ≠ e_b` (both link `v`), and `caseIIICandidate_supportExtensor_of_ne`
  -- collapses `F₀.supportExtensor e` to `Fv.supportExtensor e`.
  have hGv_ne : ∀ {e u w}, Gv.IsLink e u w → e ≠ e_a ∧ e ≠ e_b := by
    intro e u w hlink
    have hu : u ∈ V(Gv) := hlink.left_mem
    have hw : w ∈ V(Gv) := hlink.right_mem
    have hune : u ≠ v := fun h => hvVc (h ▸ hu)
    have hwne : w ≠ v := fun h => hvVc (h ▸ hw)
    have hGlink := hleG e u w hlink
    refine ⟨fun he => ?_, fun he => ?_⟩
    · subst he
      rcases (hG_ea).eq_and_eq_or_eq_and_eq hGlink with ⟨hh, _⟩ | ⟨hh, _⟩
      · exact hune hh.symm
      · exact hwne hh.symm
    · subst he
      rcases (hG_eb).eq_and_eq_or_eq_and_eq hGlink with ⟨hh, _⟩ | ⟨hh, _⟩
      · exact hune hh.symm
      · exact hwne hh.symm
  have hF₀_ext_Gv : ∀ {e u w}, Gv.IsLink e u w → F₀.supportExtensor e = Fv.supportExtensor e := by
    intro e u w hlink
    obtain ⟨hne_a, hne_b⟩ := hGv_ne hlink
    rw [hF₀, PanelHingeFramework.caseIIICandidate_supportExtensor_of_ne G ends q e_a e_b na n' nb 0
      hne_a hne_b, hseed_eq]
  -- `span Fv.rigidityRows ≤ span F₀.rigidityRows`: every `Fv`-row is an `F₀`-row.
  have hFvle : Submodule.span ℝ Fv.rigidityRows ≤ Submodule.span ℝ F₀.rigidityRows := by
    rw [Submodule.span_le]
    rintro _ ⟨e, u, w, hlink, r, hr_blk, rfl⟩
    rw [hFv, PanelHingeFramework.toBodyHinge_graph, PanelHingeFramework.ofNormals_graph] at hlink
    refine Submodule.subset_span ⟨e, u, w, hleG e u w hlink, r, ?_, rfl⟩
    rw [BodyHingeFramework.mem_hingeRowBlock_iff, hF₀_ext_Gv hlink,
      ← BodyHingeFramework.mem_hingeRowBlock_iff]
    exact hr_blk
  -- (i) The bottom transport: per `j`, a row `w̃ j` in `span F₀.rigidityRows` whose `Φ ∘ Pv`-
  -- composite is `w j`.
  have htransport : ∀ j, ∃ wt : Module.Dual ℝ (α → ScrewSpace k),
      ((wt.comp Φ.toLinearMap).comp Pv = w j) ∧ wt ∈ Submodule.span ℝ F₀.rigidityRows := by
    intro j
    rcases hwmem j with hgen | ⟨ρ', hρ'e₀, hwj⟩
    · -- A genuine `G_v`-row `hingeRow u w' r'` (`u, w' ≠ v`): brick 2 leaves it fixed, and it is
      -- an `F₀`-row by `hFvle ∘ subset_span`.
      refine ⟨w j, ?_, hFvle (Submodule.subset_span hgen)⟩
      -- The `Fv`-row form `w j = hingeRow u w' r'` with `v ≠ u, v ≠ w'` (the endpoints are in
      -- `V(Gv)`, so `≠ v`); brick 2 with `g.comp (single v) = 0` from `hingeRow_comp_single_off`.
      obtain ⟨e, u, w', hlink, r', -, hwj⟩ := hgen
      rw [hFv, PanelHingeFramework.toBodyHinge_graph,
        PanelHingeFramework.ofNormals_graph] at hlink
      have hune : v ≠ u := fun h => hvVc (h ▸ hlink.left_mem)
      have hwne : v ≠ w' := fun h => hvVc (h ▸ hlink.right_mem)
      rw [hwj]
      exact BodyHingeFramework.comp_columnOp_comp_offProj_of_single_eq_zero hva
        (BodyHingeFramework.hingeRow_comp_single_off hune hwne r')
    · -- A transported `ρ'`-row: enter as `hingeRow v b ρ'`, composite = `hingeRow a b ρ' = w j`
      -- (brick 1), and `hingeRow v b ρ'` is a genuine `e_b`-row of `F₀` (`ρ'(C(e₀)) = 0`, `t = 0`).
      refine ⟨BodyHingeFramework.hingeRow v b ρ', ?_, ?_⟩
      · rw [BodyHingeFramework.hingeRow_comp_columnOp_comp_offProj hva hvb ρ', hwj]
      · refine Submodule.subset_span ⟨e_b, v, b, hG_eb, ρ', ?_, rfl⟩
        rw [BodyHingeFramework.mem_hingeRowBlock_iff, hsuppeb]
        exact hρ'e₀
  choose wtil hwtilcomp hwtilmem using htransport
  -- `hbotrestrict`: the operated `wtil`-family is `w`, LI by `hw`.
  have hbotrestrict : LinearIndependent ℝ
      (fun j : ιb => ((wtil j).comp Φ.toLinearMap).comp Pv) := by
    have : (fun j : ιb => ((wtil j).comp Φ.toLinearMap).comp Pv) = w := funext hwtilcomp
    rw [this]; exact hw
  -- (ii) W6c certifies the restriction-form family at `F₀`.
  obtain ⟨sn, hsn_e, hsn_card, hfam⟩ :=
    PanelHingeFramework.case_III_full_family_restriction F₀ ends hva hends_ea hane
      hbotrestrict ρ hr
  -- (iii) Every member lies in `span F₀.rigidityRows`. Assemble the span-containment.
  set fam := Sum.elim
      (Sum.elim (fun i : sn => F₀.panelRow ends (i : β × _ × _))
        (fun _ : Unit => BodyHingeFramework.hingeRow (k := k) (α := α) v a ρ))
      wtil with hfam_def
  have hmem : ∀ x, fam x ∈ Submodule.span ℝ F₀.rigidityRows := by
    rintro ((⟨i, hi⟩ | u) | j)
    · -- `sn`-row: a genuine `F₀`-panel row of the candidate link `e_a` (`= (v, a)`).
      refine Submodule.subset_span (F₀.panelRow_mem_rigidityRows (i := (i : β × _ × _)) ?_)
      have he : (i : β × _ × _).1 = e_a := hsn_e _ hi
      rw [he, hends_ea]; exact hG_ea
    · -- The candidate row collapses to `hingeRow v b ρ − hingeRow a b ρ` (eq. (6.27)).
      change BodyHingeFramework.hingeRow (k := k) (α := α) v a ρ ∈ Submodule.span ℝ F₀.rigidityRows
      rw [← BodyHingeFramework.hingeRow_sub_hingeRow_eq v a b ρ]
      refine Submodule.sub_mem _ (Submodule.subset_span ⟨e_b, v, b, hG_eb, ρ, ?_, rfl⟩)
        (hFvle hρGv)
      rw [BodyHingeFramework.mem_hingeRowBlock_iff, hsuppeb]; exact hρe₀
    · exact hwtilmem j
  have hsub : Submodule.span ℝ (Set.range fam) ≤ Submodule.span ℝ F₀.rigidityRows := by
    rw [Submodule.span_le]; rintro _ ⟨x, rfl⟩; exact hmem x
  -- (iv) Count: the family is `(sn ⊕ Unit) ⊕ ιb` of card `D·(|V(G)|−1)`. The index is finite (an
  -- LI family in the finite-dimensional dual `Module.Dual ℝ (α → ScrewSpace k)`).
  haveI hfin_idx : Finite ((↥sn ⊕ Unit) ⊕ ιb) := hfam.finite
  haveI : Finite ↥sn :=
    Finite.of_injective (fun x : ↥sn => (Sum.inl (Sum.inl x) : (↥sn ⊕ Unit) ⊕ ιb))
      (fun _ _ h => by simpa using h)
  haveI : Fintype ↥sn := Fintype.ofFinite _
  haveI : Fintype ((↥sn ⊕ Unit) ⊕ ιb) := Fintype.ofFinite _
  have hcard : Nat.card ((↥sn ⊕ Unit) ⊕ ιb) = screwDim k * (V(G).ncard - 1) := by
    rw [Nat.card_sum, Nat.card_sum, hsn_card, hwcard, Nat.card_unique, hVcard]
    -- `D ≥ 1` (`(k+2).choose 2 ≥ 1`) and `m_v ≥ 1`: write `m_v = m' + 1`, expand `D·(m'+1)`.
    have hD : 1 ≤ screwDim k := Nat.choose_pos (by omega)
    obtain ⟨m', hm'⟩ : ∃ m', V(Gv).ncard = m' + 1 := ⟨V(Gv).ncard - 1, by omega⟩
    rw [hm', Nat.add_sub_cancel, Nat.add_sub_cancel, Nat.mul_succ]
    omega
  rw [← hcard, Nat.card_eq_fintype_card, ← finrank_span_eq_card hfam]
  exact Submodule.finrank_mono hsub

/-- **W7 — the M₁ arm closer: certify-then-rebase realizes the `d = 3` candidate at full rank**
(`lem:case-II-realization` / `lem:case-III`, the role-parametric arm of the `hcand` discharge;
Katoh–Tanigawa 2011 §6.4.1, eqs. (6.29)/(6.30), the certify-then-rebase route of design
§1.51(a)/(h),
Phase 22h). Given the unpacked split context — fresh body `v ∉ V(Gᵥ)` joined to `a, b ∈ V(Gᵥ)` by
the two re-inserted hinges `e_a = va`, `e_b = vb`, the IH-rigid old subgraph `Gᵥ`, the witness
second normal `n'` of `Π(a)` with its transversality data (`hLn`, `hgab`), and W6b's candidate /
bottom-row package (`ρ`, `w`) — produces `HasGenericFullRankRealization k G`.

The route is KT's own reading of eq. (6.29) ("if the top-left `6×6` block is full rank then
`rank R(G,p₁) = 6(|V|−1)`", p. 684), a statement about the *rank* of `R(G,p₁)`, not a distinguished
row family. (i) W6d certifies the (6.29) count at the hinge-level framework
`F₀ := caseIIICandidate G ends q e_a e_b n_a n' n_b 0` as the rank bound
`D(|V(G)|−1) ≤ finrank (span F₀.rigidityRows)`. (ii) W6e re-extracts from that rank a *literal*
`F₀.panelRow` family of exactly `D(|V(G)|−1)` linking edges — each slot an
`annihRow`-of-the-edge-extensor row, polynomial in the shear. (iii) W6f transfers that family along
the one-parameter `t`-family `F(t)` to a good `t^* ≠ 0` outside the GAP-3 bad set
(`setOf_not_shear_linearIndependent_subsingleton`), keeping it linearly independent and forcing
`![n_a + t^*·n', n_b]` independent (the reproduced `vb`-hinge stays transversal). (iv) Each
`F(t^*)`-slot lies in `span (ofNormals G ends q₀).rigidityRows`, where `q₀` shears `v` along
`n_a + t^*·n'`: the `e_b`-slot and the `Gᵥ`-slots have extensors *equal* to the sheared seed's (the
`e_b`-normals are `(n_a + t^*·n', n_b)` exactly; the `Gᵥ`-endpoints avoid `v`), so they are genuine
rows, while the candidate `e_a`-slot is `(-1/t^*) •` the genuine `e_a`-row
(`panelSupportExtensor_add_smul_left` makes the sheared `e_a`-extensor `(-t^*) • C(L)`, `annihRow`
linear in the extensor scales the row, and `t^* ≠ 0` inverts). (v)
`isInfinitesimallyRigidOn_vertexSet_of_span_le_rigidityRows` gives rigidity on `V(G)` at
`ofNormals G ends q₀`, and GAP-2 `hasGenericFullRankRealization_of_rigidOn_ofNormals` upgrades
to the generic motive.

Role-parametric over `(v, a, b, e_a, e_b, n')` so that W8 (the M₂ arm) is the instantiation at the
swapped roles `a ↔ b` with `ρ' := -ρ`. **§38:** the only concrete carrier reached is
`ofNormals G ends q₀` in (iv)–(v); every extensor evaluation goes through the W6a simp lemmas plus
`toBodyHinge_supportExtensor`/`ofNormals_normal` and the funext-`if_neg` `q₀`-override pattern, and
every membership is an explicit link witness (the `hrow_mem` idiom, never `whnf` on the carrier). -/
theorem PanelHingeFramework.case_III_arm_realization
    [Finite α] [Finite β]
    (G Gv : Graph α β) (ends : β → α × α) {q : α × Fin (k + 2) → ℝ}
    {v a b : α} {e_a e_b : β}
    (hvVc : v ∉ V(Gv)) (haVc : a ∈ V(Gv)) (hbVc : b ∈ V(Gv))
    (hG_ea : G.IsLink e_a v a) (hG_eb : G.IsLink e_b v b)
    (hends_ea : ends e_a = (v, a)) (hends_eb : ends e_b = (v, b)) (heab : e_a ≠ e_b)
    (hleG : ∀ e u w, Gv.IsLink e u w → G.IsLink e u w)
    (hsplitG : ∀ e u w, G.IsLink e u w → e = e_a ∨ e = e_b ∨ Gv.IsLink e u w)
    (hends_Gv : ∀ e u w, Gv.IsLink e u w → Gv.IsLink e (ends e).1 (ends e).2)
    (hne_Gv : ∀ e, Gv.IsLink e (ends e).1 (ends e).2 →
      (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge.supportExtensor e ≠ 0)
    (hVone : 1 ≤ V(Gv).ncard) (hVcard : V(G).ncard = V(Gv).ncard + 1)
    {n' : Fin (k + 2) → ℝ}
    (hLn : LinearIndependent ℝ ![(fun i => q (a, i)), n'])
    (hgab : LinearIndependent ℝ ![(fun i => q (a, i)), (fun i => q (b, i))])
    {ρ : Module.Dual ℝ (ScrewSpace k)}
    (hρgate : ρ (panelSupportExtensor (fun i => q (a, i)) n') ≠ 0)
    (hρe₀ : ρ (panelSupportExtensor (fun i => q (a, i)) (fun i => q (b, i))) = 0)
    (hρGv : BodyHingeFramework.hingeRow a b ρ ∈ Submodule.span ℝ
      (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge.rigidityRows)
    {ιb : Type*} [Finite ιb] {w : ιb → Module.Dual ℝ (α → ScrewSpace k)}
    (hwcard : Nat.card ιb = screwDim k * (V(Gv).ncard - 1))
    (hw : LinearIndependent ℝ w)
    (hwmem : ∀ j, w j ∈ (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge.rigidityRows ∨
      ∃ ρ' : Module.Dual ℝ (ScrewSpace k),
        ρ' (panelSupportExtensor (fun i => q (a, i)) (fun i => q (b, i))) = 0 ∧
        w j = BodyHingeFramework.hingeRow a b ρ')
    {n : ℕ} (hdef : G.deficiency n = 0) :
    PanelHingeFramework.HasGenericFullRankRealization k n G := by
  classical
  haveI : Fintype α := Fintype.ofFinite α
  set na := (fun i => q (a, i)) with hna
  set nb := (fun i => q (b, i)) with hnb
  have hva : v ≠ a := fun h => hvVc (h ▸ haVc)
  have hvb : v ≠ b := fun h => hvVc (h ▸ hbVc)
  have hnev : V(G).Nonempty := ⟨v, hG_ea.left_mem⟩
  -- (i) W6d: the (6.29) rank lower bound at the `t = 0` candidate framework `F₀`.
  set F₀ := PanelHingeFramework.caseIIICandidate G ends q e_a e_b na n' nb 0 with hF₀
  have hVoneG : 1 ≤ V(Gv).ncard := hVone
  have hrank : screwDim k * (V(G).ncard - 1)
      ≤ Module.finrank ℝ (Submodule.span ℝ F₀.rigidityRows) :=
    PanelHingeFramework.case_III_rank_certification G Gv ends hvVc haVc hbVc hG_ea hG_eb
      hends_ea hends_eb heab hleG hVone hVcard hLn hρgate hρe₀ hρGv hwcard hw hwmem
  -- The candidate / reproduced extensors at `F₀` (W6a simp lemmas), and their nonvanishing.
  have hsuppea : F₀.supportExtensor e_a = panelSupportExtensor na n' :=
    PanelHingeFramework.caseIIICandidate_supportExtensor_candidate G ends q na n' nb 0 heab
  have hsuppeb : F₀.supportExtensor e_b = panelSupportExtensor na nb := by
    rw [hF₀, PanelHingeFramework.caseIIICandidate_supportExtensor_reproduced, zero_smul, add_zero]
  -- (ii) W6e at `F₀`: the rank re-extracts that many literal linking `F₀.panelRow`s.
  -- `hends` at `F₀.graph = G`: every `G`-link is `e_a`, `e_b`, or a `Gᵥ`-link (`hsplitG`).
  have hF₀graph : F₀.graph = G := by rw [hF₀]; exact PanelHingeFramework.caseIIICandidate_graph ..
  -- `hends`/`hne` at `G` (= `F₀.graph` definitionally), shared by W6e and the GAP-2 close.
  have hends_q₀ : ∀ e u w, G.IsLink e u w → G.IsLink e (ends e).1 (ends e).2 := by
    intro e u w hlink
    rcases hsplitG e u w hlink with he | he | hGv
    · rw [he, hends_ea]; exact hG_ea
    · rw [he, hends_eb]; exact hG_eb
    · exact hleG e _ _ (hends_Gv e u w hGv)
  have hends_G : ∀ e u w, F₀.graph.IsLink e u w → F₀.graph.IsLink e (ends e).1 (ends e).2 :=
    hF₀graph ▸ hends_q₀
  -- `hne` on linking edges: `e_a ↦ C(L) ≠ 0` (`hLn`), `e_b ↦ C(e₀) ≠ 0` (`hgab`), `Gᵥ` via `hne_Gv`
  -- + extensor agreement off `{e_a, e_b}`.
  have hGv_off : ∀ {e u w}, Gv.IsLink e u w → e ≠ e_a ∧ e ≠ e_b := by
    intro e u w hlink
    have hune : u ≠ v := fun h => hvVc (h ▸ hlink.left_mem)
    have hwne : w ≠ v := fun h => hvVc (h ▸ hlink.right_mem)
    have hGlink := hleG e u w hlink
    refine ⟨fun he => ?_, fun he => ?_⟩
    · subst he
      rcases (hG_ea).eq_and_eq_or_eq_and_eq hGlink with ⟨hh, _⟩ | ⟨hh, _⟩
      · exact hune hh.symm
      · exact hwne hh.symm
    · subst he
      rcases (hG_eb).eq_and_eq_or_eq_and_eq hGlink with ⟨hh, _⟩ | ⟨hh, _⟩
      · exact hune hh.symm
      · exact hwne hh.symm
  have hne_F₀ : ∀ e, F₀.graph.IsLink e (ends e).1 (ends e).2 → F₀.supportExtensor e ≠ 0 := by
    intro e hlink
    rcases hsplitG e (ends e).1 (ends e).2 hlink with he | he | hGv
    · rw [he, hsuppea]; exact (panelSupportExtensor_ne_zero_iff na n').mpr hLn
    · rw [he, hsuppeb]; exact (panelSupportExtensor_ne_zero_iff na nb).mpr hgab
    · obtain ⟨hne_a, hne_b⟩ := hGv_off hGv
      rw [hF₀, PanelHingeFramework.caseIIICandidate_supportExtensor_of_ne G ends q e_a e_b na n' nb
        0 hne_a hne_b]
      exact hne_Gv e (hends_Gv e _ _ hGv)
  obtain ⟨s, hs_link, hs_card, hs_indep⟩ :=
    F₀.exists_independent_panelRow_subfamily_of_le_finrank (ends := ends) hends_G hne_F₀ hrank
  -- (iii) W6f: transfer the re-extracted family to a good `t^* ≠ 0` outside the GAP-3 bad set.
  haveI : Finite ↥s := Set.Finite.to_subtype (Set.toFinite s)
  set bad : Finset ℝ :=
    (setOf_not_shear_linearIndependent_subsingleton na n' nb hgab).finite.toFinset with hbad
  obtain ⟨t, ht_bad, ht_ne, ht_li⟩ :=
    PanelHingeFramework.caseIIICandidate_exists_good_shear G ends q heab na n' nb
      (ι := ↥s) (fun i => (i : β × _ × _)) (by rw [← hF₀]; exact hs_indep) bad
  -- `t ∉ bad` forces `![na + t·n', nb]` independent (the reproduced `vb`-hinge stays transversal).
  have hnewtrans : LinearIndependent ℝ ![na + t • n', nb] := by
    by_contra hdep
    refine ht_bad ?_
    rw [hbad, Set.Finite.mem_toFinset]
    exact hdep
  -- (iv) The sheared seed `q₀ : v ↦ na + t·n'`, agreeing with `q` off `v`.
  set Ft := PanelHingeFramework.caseIIICandidate G ends q e_a e_b na n' nb t with hFt
  set q₀ : α × Fin (k + 2) → ℝ := fun p => if p.1 = v then (na + t • n') p.2 else q p with hq₀def
  set FG₀ := (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge with hFG₀
  have hq₀v : (fun i => q₀ (v, i)) = na + t • n' := by funext i; rw [hq₀def]; simp
  have hq₀a : (fun i => q₀ (a, i)) = na := by
    funext i; rw [hq₀def, hna]; simp only [if_neg hva.symm]
  have hq₀b : (fun i => q₀ (b, i)) = nb := by
    funext i; rw [hq₀def, hnb]; simp only [if_neg hvb.symm]
  -- Off `v`, `q₀` agrees with `q`, so the `ofNormals G ends q₀` extensor of any edge avoiding `v`
  -- equals the `ofNormals G ends q` one (= `F₀`/`Ft`'s seed off `{e_a, e_b}`).
  have hq₀_off : ∀ u, u ≠ v → (fun i => q₀ (u, i)) = (fun i => q (u, i)) := by
    intro u hu; funext i; rw [hq₀def]; simp only [if_neg hu]
  -- The genuine `FG₀`-extensors at the three relevant kinds of edge.
  have hFG₀_ea : FG₀.supportExtensor e_a = (-t) • panelSupportExtensor na n' := by
    rw [hFG₀, PanelHingeFramework.toBodyHinge_supportExtensor, PanelHingeFramework.ofNormals_ends,
      PanelHingeFramework.ofNormals_normal, PanelHingeFramework.ofNormals_normal, hends_ea]
    simp only [hq₀v, hq₀a, panelSupportExtensor_add_smul_left]
  have hFG₀_eb : FG₀.supportExtensor e_b = panelSupportExtensor (na + t • n') nb := by
    rw [hFG₀, PanelHingeFramework.toBodyHinge_supportExtensor, PanelHingeFramework.ofNormals_ends,
      PanelHingeFramework.ofNormals_normal, PanelHingeFramework.ofNormals_normal, hends_eb]
    simp only [hq₀v, hq₀b]
  have hFt_eb : Ft.supportExtensor e_b = panelSupportExtensor (na + t • n') nb := by
    rw [hFt, PanelHingeFramework.caseIIICandidate_supportExtensor_reproduced]
  have hFt_ea : Ft.supportExtensor e_a = panelSupportExtensor na n' :=
    PanelHingeFramework.caseIIICandidate_supportExtensor_candidate G ends q na n' nb t heab
  -- A `Gᵥ`-edge keeps both `Ft` and `FG₀` at the `q`-seed extensor (its endpoints avoid `v`).
  have hGv_seed_eq : ∀ {e u w}, Gv.IsLink e u w →
      Ft.supportExtensor e = FG₀.supportExtensor e := by
    intro e u w hlink
    obtain ⟨hne_a, hne_b⟩ := hGv_off hlink
    -- the *recorded* endpoints of `e` lie in `V(Gᵥ)` (via `hends_Gv`), so both avoid `v`, hence
    -- `q₀` agrees with `q` at each.
    have hrec := hends_Gv e u w hlink
    have hfst : (ends e).1 ≠ v := fun h => hvVc (h ▸ hrec.left_mem)
    have hsnd : (ends e).2 ≠ v := fun h => hvVc (h ▸ hrec.right_mem)
    rw [hFt, PanelHingeFramework.caseIIICandidate_supportExtensor_of_ne G ends q e_a e_b na n' nb t
        hne_a hne_b, hFG₀, PanelHingeFramework.toBodyHinge_supportExtensor,
      PanelHingeFramework.toBodyHinge_supportExtensor, PanelHingeFramework.ofNormals_ends,
      PanelHingeFramework.ofNormals_ends, PanelHingeFramework.ofNormals_normal,
      PanelHingeFramework.ofNormals_normal, PanelHingeFramework.ofNormals_normal,
      PanelHingeFramework.ofNormals_normal, hq₀_off (ends e).1 hfst, hq₀_off (ends e).2 hsnd]
  -- `FG₀.graph = G` definitionally (`toBodyHinge_graph`/`ofNormals_graph` are `rfl`), so a `G`-link
  -- is an `FG₀`-link and `panelRow_mem_rigidityRows_of_link` applies directly.
  have hFG₀_eq_panelRow : ∀ {e u w} (t₁ t₂ : Set.powersetCard (Fin (k + 2)) k),
      ends e = (u, w) → Ft.supportExtensor e = FG₀.supportExtensor e →
      Ft.panelRow ends (e, t₁, t₂) = FG₀.panelRow ends (e, t₁, t₂) := by
    intro e u w t₁ t₂ hends_e hext
    rw [Ft.panelRow_eq_hingeRow_annihRow_of_ends ends hends_e,
      FG₀.panelRow_eq_hingeRow_annihRow_of_ends ends hends_e, hext]
  -- The candidate `e_a`-slot: `Ft`-row is `(-1/t) •` the genuine `FG₀` `e_a`-row (extracted as a
  -- standalone fact to avoid substituting `e_a`/`e_b` away in the `hmem` dispatch).
  have hmem_ea : ∀ t₁ t₂, Ft.panelRow ends (e_a, t₁, t₂) ∈ Submodule.span ℝ FG₀.rigidityRows := by
    intro t₁ t₂
    have hFtrow : Ft.panelRow ends (e_a, t₁, t₂)
        = BodyHingeFramework.hingeRow v a (annihRow (panelSupportExtensor na n') t₁ t₂) := by
      rw [Ft.panelRow_eq_hingeRow_annihRow_of_ends ends hends_ea, hFt_ea]
    have hFG₀row : FG₀.panelRow ends (e_a, t₁, t₂)
        = (-t) • BodyHingeFramework.hingeRow v a (annihRow (panelSupportExtensor na n') t₁ t₂) := by
      rw [FG₀.panelRow_eq_hingeRow_annihRow_of_ends ends hends_ea, hFG₀_ea, annihRow_smul,
        BodyHingeFramework.hingeRow_eq_dualMap, map_smul, ← BodyHingeFramework.hingeRow_eq_dualMap]
    have hmem_genuine : FG₀.panelRow ends (e_a, t₁, t₂) ∈ Submodule.span ℝ FG₀.rigidityRows :=
      Submodule.subset_span (FG₀.panelRow_mem_rigidityRows_of_link ends hends_ea hG_ea t₁ t₂)
    rw [hFtrow,
      show BodyHingeFramework.hingeRow v a (annihRow (panelSupportExtensor na n') t₁ t₂)
        = (-t)⁻¹ • FG₀.panelRow ends (e_a, t₁, t₂) from by
          rw [hFG₀row, smul_smul, inv_mul_cancel₀ (neg_ne_zero.mpr ht_ne), one_smul]]
    exact Submodule.smul_mem _ _ hmem_genuine
  -- Membership of each `Ft`-slot in `span FG₀.rigidityRows`.
  have hmem : ∀ i : ↥s, Ft.panelRow ends (i : β × _ × _) ∈ Submodule.span ℝ FG₀.rigidityRows := by
    rintro ⟨⟨e, t₁, t₂⟩, hi⟩
    have hlink : G.IsLink e (ends e).1 (ends e).2 := hs_link _ hi
    change Ft.panelRow ends (e, t₁, t₂) ∈ Submodule.span ℝ FG₀.rigidityRows
    rcases hsplitG e (ends e).1 (ends e).2 hlink with he | he | hGv
    · -- `e = e_a`: the candidate slot, via `hmem_ea`.
      rw [he]; exact hmem_ea t₁ t₂
    · -- `e = e_b`: the reproduced slot, extensors agree so it is a genuine `FG₀`-row.
      rw [he, hFG₀_eq_panelRow t₁ t₂ hends_eb (by rw [hFt_eb, hFG₀_eb])]
      exact Submodule.subset_span (FG₀.panelRow_mem_rigidityRows_of_link ends hends_eb hG_eb t₁ t₂)
    · -- A `Gᵥ`-slot: extensors agree (`hGv_seed_eq`), so `Ft`-row is a genuine `FG₀`-row.
      rw [hFG₀_eq_panelRow t₁ t₂ (Prod.mk.eta (p := ends e)) (hGv_seed_eq hGv)]
      exact Submodule.subset_span (FG₀.panelRow_mem_rigidityRows_of_link ends
        (Prod.mk.eta (p := ends e)) (hleG e _ _ (hends_Gv e _ _ hGv)) t₁ t₂)
  -- (v) Rigidity on `V(G)` at `q₀`, then GAP-2 upgrades to the generic motive.
  have hsub : Submodule.span ℝ
      (Set.range (fun i : ↥s => Ft.panelRow ends (i : β × _ × _)))
      ≤ Submodule.span ℝ FG₀.rigidityRows := by
    rw [Submodule.span_le]; rintro _ ⟨i, rfl⟩; exact hmem i
  have hFG₀graph : FG₀.graph.vertexSet = V(G) := by
    rw [hFG₀, PanelHingeFramework.toBodyHinge_graph, PanelHingeFramework.ofNormals_graph]
  have hcard_s : screwDim k * (V(G).ncard - 1) ≤ Nat.card ↥s := hs_card.ge
  -- Feed the lemma at its own `FG₀.graph.vertexSet` shape (via `hFG₀graph`), then read the
  -- conclusion back as `V(G)` — `FG₀.graph = G` by `rfl`, so no defeq-check forces the heavy
  -- `q₀`-seed open (TACTICS-QUIRKS §38).
  -- GAP-2 `hne` at `q₀`: the linking-edge extensors are nonzero (`e_a ↦ (-t)·C(L)`, `e_b ↦ C(e₀)`
  -- at the sheared `vb`, `Gᵥ` via `hne_Gv` through the `Ft`/`FG₀` extensor agreement).
  have hne_q₀ : ∀ e, G.IsLink e (ends e).1 (ends e).2 →
      (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.supportExtensor e ≠ 0 := by
    intro e hlink
    rw [show (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge = FG₀ from hFG₀.symm]
    rcases hsplitG e (ends e).1 (ends e).2 hlink with he | he | hGv
    · rw [he, hFG₀_ea]
      exact smul_ne_zero (neg_ne_zero.mpr ht_ne)
        ((panelSupportExtensor_ne_zero_iff na n').mpr hLn)
    · rw [he, hFG₀_eb]; exact (panelSupportExtensor_ne_zero_iff (na + t • n') nb).mpr hnewtrans
    · rw [← hGv_seed_eq hGv]
      obtain ⟨hne_a, hne_b⟩ := hGv_off hGv
      rw [hFt, PanelHingeFramework.caseIIICandidate_supportExtensor_of_ne G ends q e_a e_b na n' nb
        t hne_a hne_b]
      exact hne_Gv e (hends_Gv e _ _ hGv)
  -- (v) Rigidity on `V(G)` at `q₀` — generalize the heavy `Ft.panelRow`-family to a plain `f` so
  -- the `_of_span_le_rigidityRows` application never `whnf`s the `caseIIICandidate` carrier (§38),
  -- then GAP-2 upgrades to the generic motive.
  rw [hFG₀] at hsub
  set f : ↥s → Module.Dual ℝ (α → ScrewSpace k) := fun i => Ft.panelRow ends (i : β × _ × _)
    with hf_def
  clear_value f
  have hG : (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.graph.vertexSet = V(G) := rfl
  have hrig :=
    BodyHingeFramework.isInfinitesimallyRigidOn_vertexSet_of_span_le_rigidityRows
      (F := (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge)
      ht_li hsub (by rw [hG]; exact hnev) (by rw [hG]; exact hcard_s)
  rw [hG] at hrig
  exact PanelHingeFramework.hasGenericFullRankRealization_of_rigidOn_ofNormals G ends hends_q₀
    hne_q₀ hnev hrig n hdef

/-- **W8 — the M₂ arm closer: the candidate at `e_b` realizes the `d = 3` framework at full rank**
(`lem:case-II-realization` / `lem:case-III`, the second of the three `hcand`-discharge arms;
Katoh–Tanigawa 2011 §6.4.1, eq. (6.42)'s `M₂ = (r(L'); r̂)`, the swapped-role instantiation of
design §1.51(i), Phase 22h). The M₂ arm carries the candidate line `L' ⊂ Π(b)` (the second
normal `n''` of body `b`'s panel), so the witness gate sits at the `b`-side
(`hρgate : ρ (panelSupportExtensor n_b n'') ≠ 0`, the `u = 1` discriminator branch). Everything
tied to the inductive `(ab)`-row — the candidate functional `ρ`, its annihilation `ρ(C(e₀)) = 0`,
its `Gᵥ`-row membership `hingeRow a b ρ ∈ span`, and the bottom family `w` — is **identical** to
W7's (KT p. 686: "the same `λ_{(ab)j}` and the index `i^*` are used"), so W10 feeds both arms from
one W6b invocation; only `hLn`/`hρgate` move to the `b`-side.

This is a pure instantiation of `case_III_arm_realization` at the swapped roles
`(a, b, e_a, e_b, n') := (b, a, e_b, e_a, n'')`, feeding `ρ' := -ρ`: the swapped-role candidate
functional is `-ρ` because `r̂ = hingeRow a b ρ = hingeRow b a (-ρ)` (`hingeRow_swap`) — a
Lean-orientation artifact, not a KT discrepancy (KT p. 681: "`r'` is indeed equal to `r`"; the
row content is identical). The hypothesis conversions are `hingeRow_swap`, `LinearMap.neg_apply`
(the functional-side `(-ρ) x = -(ρ x)`) + `panelSupportExtensor_swap` + `map_neg`, and
`LinearIndependent.pair_symm_iff`. Graph-free over the carrier (it only reorders data and rewrites
functionals); the §38 trap lives inside W7. -/
theorem PanelHingeFramework.case_III_arm_realization_M2
    [Finite α] [Finite β]
    (G Gv : Graph α β) (ends : β → α × α) {q : α × Fin (k + 2) → ℝ}
    {v a b : α} {e_a e_b : β}
    (hvVc : v ∉ V(Gv)) (haVc : a ∈ V(Gv)) (hbVc : b ∈ V(Gv))
    (hG_ea : G.IsLink e_a v a) (hG_eb : G.IsLink e_b v b)
    (hends_ea : ends e_a = (v, a)) (hends_eb : ends e_b = (v, b)) (heab : e_a ≠ e_b)
    (hleG : ∀ e u w, Gv.IsLink e u w → G.IsLink e u w)
    (hsplitG : ∀ e u w, G.IsLink e u w → e = e_a ∨ e = e_b ∨ Gv.IsLink e u w)
    (hends_Gv : ∀ e u w, Gv.IsLink e u w → Gv.IsLink e (ends e).1 (ends e).2)
    (hne_Gv : ∀ e, Gv.IsLink e (ends e).1 (ends e).2 →
      (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge.supportExtensor e ≠ 0)
    (hVone : 1 ≤ V(Gv).ncard) (hVcard : V(G).ncard = V(Gv).ncard + 1)
    {n'' : Fin (k + 2) → ℝ}
    -- the candidate line `L' ⊂ Π(b)`: the witness normal `n''` is transversal to `n_b`
    (hLn : LinearIndependent ℝ ![(fun i => q (b, i)), n''])
    (hgab : LinearIndependent ℝ ![(fun i => q (a, i)), (fun i => q (b, i))])
    {ρ : Module.Dual ℝ (ScrewSpace k)}
    -- the gate at the `b`-side line (the `u = 1` discriminator witness)
    (hρgate : ρ (panelSupportExtensor (fun i => q (b, i)) n'') ≠ 0)
    (hρe₀ : ρ (panelSupportExtensor (fun i => q (a, i)) (fun i => q (b, i))) = 0)
    (hρGv : BodyHingeFramework.hingeRow a b ρ ∈ Submodule.span ℝ
      (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge.rigidityRows)
    {ιb : Type*} [Finite ιb] {w : ιb → Module.Dual ℝ (α → ScrewSpace k)}
    (hwcard : Nat.card ιb = screwDim k * (V(Gv).ncard - 1))
    (hw : LinearIndependent ℝ w)
    (hwmem : ∀ j, w j ∈ (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge.rigidityRows ∨
      ∃ ρ' : Module.Dual ℝ (ScrewSpace k),
        ρ' (panelSupportExtensor (fun i => q (a, i)) (fun i => q (b, i))) = 0 ∧
        w j = BodyHingeFramework.hingeRow a b ρ')
    {n : ℕ} (hdef : G.deficiency n = 0) :
    PanelHingeFramework.HasGenericFullRankRealization k n G := by
  classical
  -- Feed W7 at the swapped roles `a ↔ b`, `e_a ↔ e_b`, with `ρ' := -ρ`. The candidate row content
  -- is invariant: `hingeRow a b ρ = hingeRow b a (-ρ)`.
  refine PanelHingeFramework.case_III_arm_realization (k := k) G Gv ends
    hvVc hbVc haVc hG_eb hG_ea hends_eb hends_ea heab.symm hleG
    (fun e u w hlink => by
      rcases hsplitG e u w hlink with h | h | h
      exacts [Or.inr (Or.inl h), Or.inl h, Or.inr (Or.inr h)])
    hends_Gv hne_Gv hVone hVcard hLn (LinearIndependent.pair_symm_iff.mp hgab)
    (ρ := -ρ) ?_ ?_ ?_ (ιb := ιb) (w := w) hwcard hw ?_ hdef
  -- `hρgate`: `(-ρ)(panelSupportExtensor n_b n'') ≠ 0` from `hρgate` (negation on the functional).
  · rw [LinearMap.neg_apply, neg_ne_zero]; exact hρgate
  -- `hρe₀`: `(-ρ)(panelSupportExtensor n_b n_a) = 0` from `hρe₀` via `panelSupportExtensor_swap`.
  · rw [LinearMap.neg_apply, panelSupportExtensor_swap, map_neg, hρe₀, neg_zero, neg_zero]
  -- `hρGv`: `hingeRow b a (-ρ) ∈ span` is `hingeRow a b ρ ∈ span` (`hingeRow_swap`).
  · rwa [← BodyHingeFramework.hingeRow_swap]
  -- `hwmem`: each `ρ'`-tagged member converts to `-ρ'` (`hingeRow b a (-ρ') = hingeRow a b ρ'`;
  -- the annihilation swaps the normals and negates the functional).
  · intro j
    rcases hwmem j with hgen | ⟨ρ', hρ'e₀, hwj⟩
    · exact Or.inl hgen
    · exact Or.inr ⟨-ρ', by rw [LinearMap.neg_apply, panelSupportExtensor_swap, map_neg, hρ'e₀,
        neg_zero, neg_zero], by rw [hwj, ← BodyHingeFramework.hingeRow_swap]⟩

/-- **L5 — the candidate-completion index map is injective** (`lem:case-II-realization` /
`lem:case-III`, the `j`/`Sum.elim` packaging leaf of the `d = 3` `hsplit` producer; Katoh–Tanigawa
2011 §6.4.1, eq. (6.29), Phase 22g). The candidate-completion assembly
(`linearIndependent_sum_{augment,p2,p3}_candidateRow`) outputs a `Sum`-indexed family
`(rn ⊕ {candidate row}) ⊕ ro` over `ι = (sn ⊕ Unit) ⊕ so`; the abstractly-indexed device feed
(`hasFullRankRealization_of_independent_panelRow_index`) consumes it along an injective index map
`j` placing each block index at its `(edge, ⋀ᵏ-pair)`. This certifies that `j` is injective — the
candidate analog of the inline `hjinj` of `case_II_placement_eq612` (which has only the
`sn ⊕ so` two-block split), with the extra `Unit` summand for the candidate row's edge `e_a`.

The `sn`-indices use the new-block edge `e_b` (`hsn_e`); the candidate `Unit`-index uses `e_a`
(the `va`-hinge of the re-inserted body `v`); the `so`-indices use `Gᵥ`-edges, none equal to `e_b`
(`hso_ne_eb`, from `case_III_old_new_blocks`) nor `e_a` (`hso_ne_ea`; both link the fresh body
`v ∉ V(Gᵥ)`). With `e_a ≠ e_b` (`heab`) the three blocks have pairwise-disjoint edge-supports, so
the map is injective: a collision within `sn` or `so` is `Subtype.val`-injectivity, and any
cross-block collision contradicts one of the three disjointness facts on the first coordinate. This
is graph-free over the carrier (it reads only the edge labels), so the recurring `ofNormals`/
`withGraph` defeq trap (TACTICS-QUIRKS §38) does not bite. -/
theorem PanelHingeFramework.candidateCompletion_index_injective
    {sn so : Set (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k)}
    {e_a e_b : β} {ta tb : Set.powersetCard (Fin (k + 2)) k} (heab : e_a ≠ e_b)
    (hsn_e : ∀ i ∈ sn, (i : β × _ × _).1 = e_b)
    (hso_ne_eb : ∀ i ∈ so, (i : β × _ × _).1 ≠ e_b)
    (hso_ne_ea : ∀ i ∈ so, (i : β × _ × _).1 ≠ e_a) :
    Function.Injective
      (Sum.elim (Sum.elim (fun i : sn => (i : β × _ × _)) (fun _ : Unit => (e_a, ta, tb)))
        (fun i : so => (i : β × _ × _)) :
        (sn ⊕ Unit) ⊕ so → β × Set.powersetCard (Fin (k + 2)) k
          × Set.powersetCard (Fin (k + 2)) k) := by
  rintro ((⟨in₁, hin₁⟩ | u₁) | ⟨io₁, hio₁⟩) ((⟨in₂, hin₂⟩ | u₂) | ⟨io₂, hio₂⟩) hab <;>
    simp only [Sum.elim_inl, Sum.elim_inr] at hab
  -- `sn` vs `sn`: `Subtype.val` injective.
  · exact congrArg (Sum.inl ∘ Sum.inl) (Subtype.ext hab)
  -- `sn` vs `Unit`: the `sn`-edge `e_b` would equal `e_a`, against `heab`.
  · exact absurd ((hsn_e _ hin₁).symm.trans (congrArg Prod.fst hab)) heab.symm
  -- `sn` vs `so`: the `so`-edge would equal `e_b`, against `hso_ne_eb`.
  · exact absurd ((congrArg Prod.fst hab).symm.trans (hsn_e _ hin₁)) (hso_ne_eb _ hio₂)
  -- `Unit` vs `sn`: symmetric to the `sn` vs `Unit` case.
  · exact absurd ((hsn_e _ hin₂).symm.trans (congrArg Prod.fst hab).symm) heab.symm
  -- `Unit` vs `Unit`: both indices are `()`.
  · rw [Subsingleton.elim u₁ u₂]
  -- `Unit` vs `so`: the `so`-edge would equal `e_a`, against `hso_ne_ea`.
  · exact absurd (congrArg Prod.fst hab).symm (hso_ne_ea _ hio₂)
  -- `so` vs `sn`: symmetric to the `sn` vs `so` case.
  · exact absurd ((congrArg Prod.fst hab).trans (hsn_e _ hin₂)) (hso_ne_eb _ hio₁)
  -- `so` vs `Unit`: symmetric to the `Unit` vs `so` case.
  · exact absurd (congrArg Prod.fst hab) (hso_ne_ea _ hio₁)
  -- `so` vs `so`: `Subtype.val` injective.
  · exact congrArg Sum.inr (Subtype.ext hab)

/-- **L5-pack — the candidate-completion `panelRow ∘ j` family identity and count**
(`lem:case-II-realization` / `lem:case-III`, a packaging leaf for the `d = 3` `hsplit` producer;
Katoh–Tanigawa 2011 §6.4.1, eq. (6.29), Phase 22g). The candidate-completion assembly
(`linearIndependent_sum_{augment,p2,p3}_candidateRow`) outputs the family
`Sum.elim (Sum.elim rn (fun _ : Unit => hingeRow u w ρ)) ro` over `(sn ⊕ Unit) ⊕ so`; this leaf
repackages it as a single `panelRow`-family `fam = fun i => F.panelRow ends (j i)` along an
injective index `j` (the shape a panelRow-shaped device feed would need), supplying both halves
once the three blocks are each a `panelRow`:

* the **OLD/NEW blocks** are `panelRow`s of `F` directly — `rn i = F.panelRow ends i.val` for
  `i : sn` and `ro i = F.panelRow ends i.val` for `i : so` (the L1 `case_III_old_new_blocks` output
  is already in `panelRow` form);
* the **`Unit`-summand candidate row** is the `panelRow` at the candidate edge `e_a` —
  `hingeRow u w ρ = F.panelRow ends (e_a, ta, tb)`, with `ρ = annihRow (C(e_a)) ta tb` and
  `ends e_a = (u, w)`, which is L3 (`panelRow_eq_hingeRow_annihRow_of_ends`). (This resolves the
  §1.34 (F1) subtlety: the producer's `ρ` is realized as a single `annihRow` pair, so the `Unit`
  summand IS one `panelRow`.)

With those, the family is *definitionally* `F.panelRow ends ∘ j` for the L5-inj index map `j`
(`Sum.elim`-of-`Sum.elim` against the matching `j`, closed by `funext`/`rcases`/`rfl`), so the
identity needs no `whnf` of the carrier (graph-free, no TACTICS-QUIRKS §38 trap). The count
`screwDim k * (V(G).ncard − 1) ≤ Nat.card ((sn ⊕ Unit) ⊕ so)` is the L1 block counts
`Nat.card sn = D − 1`, `Nat.card so = D(|V(Gᵥ)|−1)` summed over the `+1` `Unit`, with
`|V(Gᵥ)| = |V(G)| − 1`: `((D−1)+1) + D(m−2) = D(m−1)` for `m = |V(G)| ≥ 1` (the eq. (6.29)
full count `D(|V|−1)`, the `+1` over the eq. (6.12) brick's `D(|V|−1)−1`). -/
theorem PanelHingeFramework.candidateCompletion_panelRow_packaging [Finite β]
    (F : BodyHingeFramework k α β) (ends : β → α × α)
    {sn so : Set (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k)}
    {e_a : β} {ta tb : Set.powersetCard (Fin (k + 2)) k} {u w : α}
    {ρ : Module.Dual ℝ (ScrewSpace k)}
    (hends : ends e_a = (u, w)) (hρ : ρ = annihRow (F.supportExtensor e_a) ta tb)
    {mV mVv : ℕ} (hsn_card : Nat.card sn = screwDim k - 1)
    (hso_card : Nat.card so = screwDim k * (mVv - 1)) (hVcard : mVv = mV - 1) (hm : 1 ≤ mV) :
    -- the `panelRow ∘ j` family identity (the device feed's shape)
    (Sum.elim (Sum.elim (fun i : sn => F.panelRow ends (i : β × _ × _))
        (fun _ : Unit => BodyHingeFramework.hingeRow (k := k) (α := α) u w ρ))
      (fun i : so => F.panelRow ends (i : β × _ × _)) =
      fun i => F.panelRow ends
        (Sum.elim (Sum.elim (fun i : sn => (i : β × _ × _)) (fun _ : Unit => (e_a, ta, tb)))
          (fun i : so => (i : β × _ × _)) i)) ∧
    -- the eq. (6.29) full count `D(|V|−1) ≤ |(sn ⊕ Unit) ⊕ so|`
    screwDim k * (mV - 1) ≤ Nat.card ((sn ⊕ Unit) ⊕ so) := by
  refine ⟨?_, ?_⟩
  · -- The `Unit` summand is the panel row at `e_a` (L3); the rest match `j`'s components by `rfl`.
    have hcand : BodyHingeFramework.hingeRow (k := k) (α := α) u w ρ
        = F.panelRow ends (e_a, ta, tb) := by
      rw [F.panelRow_eq_hingeRow_annihRow_of_ends ends hends ta tb, hρ]
    funext i; rcases i with (i | i) | i
    · rfl
    · simp only [Sum.elim_inl, Sum.elim_inr]; exact hcand
    · rfl
  · -- `((D−1)+1) + D(m−2) = D(m−1)` for `m ≥ 1`.
    rw [Nat.card_sum, Nat.card_sum, Nat.card_unique (α := Unit), hsn_card, hso_card, hVcard]
    have hD : 1 ≤ screwDim k := Nat.choose_pos (by omega)
    obtain ⟨m, rfl⟩ : ∃ m, mV = m + 1 := ⟨mV - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    cases m with
    | zero => simp
    | succ m' => rw [Nat.add_sub_cancel, Nat.mul_succ]; omega

/-- **L2b-place (per-line realization) — the line-indexed candidate placement attains a full-rank
realization when the common vector is not orthogonal to the witness line's panel-meet**
(`lem:case-III-claim612-line-in-panel-union`, the C2-feed leaf of the `d = 3` `hsplit` producer;
Katoh–Tanigawa 2011 §6.4.1, eqs.~(6.27)–(6.44), Phase 22g). The graph-free assembly closing the gap
between the per-line independent candidate family (`case_III_full_family_of_line`) and the
realization motive `HasFullRankRealization`: it runs the per-line row-space criterion at `e_a` to
obtain the full `D(|V|−1)` candidate family `Sum.elim (Sum.elim rn {hingeRow v a r}) ro`, then feeds
it straight into the fixed-placement realization brick C1
(`hasFullRankRealization_of_independent_rigidityRow`) — the candidate `+1` row `hingeRow v a r` is
*not* a single `panelRow` (it has `r(C(e_a)) ≠ 0`, while every panelRow annihilates its edge's
extensor), so it cannot route through the panelRow-indexed device feed; but it lies in
`span rigidityRows` (the `hcand_mem` hypothesis, supplied by the consumer via
`hingeRow_mem_rigidityRows` once `r` is restricted to the `e_a`-hinge-row block), exactly C1's
`hsub` shape (§1.35).

The OLD block `ro` (the `D(|V(Gᵥ)|−1)` linking rows) enters abstractly: independent (`holdindep`),
vanishing at `v`'s screw column (`hold`, the per-line criterion's pin input), and members of
`span rigidityRows` (`hro_mem`). The `va`-hinge `e_a` is nondegenerate (`hane`) and the witness
`r(F.supportExtensor e_a) ≠ 0` (`hr`, supplied by Claim~6.12's existential join witness through the
Leaf-2b seed-from-line core) drives both the criterion (the NEW-block `sn`'s candidate-completion is
independent) and C2's selector. The count `D(|V(G)|−1) ≤ |(sn ⊕ Unit) ⊕ ιo|` is the eq.~(6.29) full
count, carried in as `hcard` (the consumer assembles it from the L1 block counts via the L5-pack
arithmetic).

Graph-free over the abstract `F` (it reads only `ends`/`supportExtensor`/`panelRow`/`hingeRow`/
`rigidityRows`); the recurring `ofNormals`/`withGraph` defeq trap (TACTICS-QUIRKS §38) is confined
to the producer's seed feed (Leaf 3), which supplies `F := ofNormals G ends q₀`,
`hane`/`hold`/`holdindep`/`hro_mem`/`hcand_mem`/`hcard`/`hr` at the concrete carrier. -/
theorem PanelHingeFramework.case_III_realization_of_line [DecidableEq α] [Finite α] [Finite β]
    (G : Graph α β) (ends : β → α × α) (hne : V(G).Nonempty)
    {q₀ : α × Fin (k + 2) → ℝ} {v a : α} {e_a : β} (hva : v ≠ a) (hends_ea : ends e_a = (v, a))
    (hG_ea : G.IsLink e_a v a)
    (hane : (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.supportExtensor e_a ≠ 0)
    {ιo : Type*} [Finite ιo] {ro : ιo → Module.Dual ℝ (α → ScrewSpace k)}
    (hold : ∀ (j : ιo) (x : ScrewSpace k), ro j (Function.update (0 : α → ScrewSpace k) v x) = 0)
    (holdindep : LinearIndependent ℝ ro)
    (hro_mem : ∀ j, ro j ∈ Submodule.span ℝ
      (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.rigidityRows)
    (r : Module.Dual ℝ (ScrewSpace k))
    (hcand_mem : BodyHingeFramework.hingeRow (k := k) (α := α) v a r ∈ Submodule.span ℝ
      (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.rigidityRows)
    (hr : r ((PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.supportExtensor e_a) ≠ 0)
    (hcard : ∀ sn : Set (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k),
      Nat.card sn = screwDim k - 1 →
      screwDim k * (V(G).ncard - 1) ≤ Nat.card ((sn ⊕ Unit) ⊕ ιo)) :
    PanelHingeFramework.HasFullRankRealization k G := by
  set F := (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge with hF
  -- (1) Run the per-line row-space criterion at `e_a`: the candidate-completion family
  -- `Sum.elim (Sum.elim rn {hingeRow v a r}) ro` is linearly independent (witness `hr`).
  obtain ⟨sn, hsn_e, hsn_card, hfam⟩ :=
    PanelHingeFramework.case_III_full_family_of_line F ends hva hends_ea hane hold holdindep r hr
  haveI : Finite ↥sn := Set.Finite.to_subtype (Set.toFinite sn)
  -- (2) Each row of the family lies in `span rigidityRows`: the `sn`-rows are panelRows of `e_a`
  -- (which links `v a` in `G`, by `hsn_e`/`hends_ea`); the `Unit` candidate row is `hcand_mem`;
  -- the OLD-block rows are `hro_mem`.
  refine PanelHingeFramework.hasFullRankRealization_of_independent_rigidityRow G ends hne
    (q₀ := q₀) hfam ?_ (hcard sn hsn_card)
  rw [Submodule.span_le, Set.range_subset_iff]
  rintro ((⟨i, hi⟩ | u) | i) <;> simp only [Sum.elim_inl, Sum.elim_inr]
  · -- `sn`-row: `panelRow` of `e_a`, a rigidity row by the direct `G`-link `e_a = va`.
    refine Submodule.subset_span ?_
    obtain ⟨e', t₁, t₂⟩ := (i : β × _ × _)
    have hi1 : e' = e_a := hsn_e _ hi
    subst hi1
    exact F.panelRow_mem_rigidityRows_of_link ends hends_ea hG_ea t₁ t₂
  · -- `Unit` candidate row `hingeRow v a r`: the `hcand_mem` hypothesis.
    exact hcand_mem
  · -- OLD-block row: the `hro_mem` hypothesis.
    exact hro_mem i

/-- **Triangle realization, generic motive** (`lem:triangle-realization`, T4; Katoh–Tanigawa 2011
§6.4, KT Lemma 6.7(i) at `m = 3`; Phase 22h). The base of the `d = 3` split-off recursion
for Case~III: a simple minimal `0`-dof-graph on exactly three vertices has the generic-motive
realization `HasGenericFullRankRealization k G`.

**Construction.** T1 (`exists_isLink_of_isMinimalKDof_card_three`) gives `V(G) = {v,a,b}` and
a third edge `f : a–b` completing the triangle. T3 (`exists_triangle_normals`) produces three
normals `n₀, n₁, n₂ ∈ ℝ^(k+2)` with pairwise nonvanishing joins and LI cyclic extensor family
`panelSupportExtensor n₀ n₁, panelSupportExtensor n₁ n₂, panelSupportExtensor n₂ n₀`. The seed
`q₀` assigns `v ↦ n₀`, `a ↦ n₁`, `b ↦ n₂` (junk elsewhere). The canonical `G.endsOf` selector
orients each edge; the support extensor of each triangle edge is ± a member of T3's LI cyclic
family (unit scalar from `endsOf` orientation), so T2 (`theorem_55_triangle`)'s independence
hypothesis holds. T2 gives rigidity on `{v,a,b} = V(G)`, and
`hasGenericFullRankRealization_of_rigidOn_ofNormals` upgrades to the generic motive. -/
theorem PanelHingeFramework.hasGenericFullRankRealization_of_triangle
    [DecidableEq β] [Finite α] [Finite β] {n : ℕ} (G : Graph α β) [G.Simple]
    (hD : 3 ≤ Graph.bodyBarDim n) (hk : 1 ≤ k)
    (hG : G.IsMinimalKDof n 0)
    (hcard : V(G).ncard = 3)
    {v a b : α} {eₐ e_b : β}
    (hG_ea : G.IsLink eₐ v a) (hG_eb : G.IsLink e_b v b)
    (hav : a ≠ v) (hbv : b ≠ v) (heab : eₐ ≠ e_b) :
    PanelHingeFramework.HasGenericFullRankRealization k n G := by
  classical
  -- T1: vertex set pin + third edge.
  obtain ⟨hab, hVeq, f, hf⟩ :=
    Graph.exists_isLink_of_isMinimalKDof_card_three hD hG hcard hG_ea hG_eb hav hbv heab
  -- T3: the triangle normals with LI cyclic extensor family and pairwise nonzero joins.
  obtain ⟨n₀, n₁, n₂, ⟨hn₀₁, hn₁₂, hn₂₀⟩, hLI⟩ := exists_triangle_normals (k := k) hk
  -- Convert T3's fun-form LI to the `![C₀,C₁,C₂]` matrix form.
  -- `fun i => panelSupportExtensor (![n₀,n₁,n₂] i) (![n₁,n₂,n₀] i)` equals
  -- `![C₀, C₁, C₂]` where `Cᵢ = panelSupportExtensor (T3 pairs)`.
  have hLI' : LinearIndependent ℝ
      ![panelSupportExtensor (k := k) n₀ n₁, panelSupportExtensor n₁ n₂,
        panelSupportExtensor n₂ n₀] := by
    have heq : (![panelSupportExtensor (k := k) n₀ n₁, panelSupportExtensor n₁ n₂,
        panelSupportExtensor n₂ n₀] : Fin 3 → _) =
        fun i => panelSupportExtensor (![n₀, n₁, n₂] i) (![n₁, n₂, n₀] i) := by
      funext i; fin_cases i <;> rfl
    rw [heq]; exact hLI
  -- Derive `panelSupportExtensor nᵢ nⱼ ≠ 0` from T3's join hypotheses.
  have hne₀₁ : panelSupportExtensor (k := k) n₀ n₁ ≠ 0 :=
    (panelSupportExtensor_ne_zero_iff n₀ n₁).mpr ((normalsJoin_ne_zero_iff n₀ n₁).mp hn₀₁)
  have hne₁₂ : panelSupportExtensor (k := k) n₁ n₂ ≠ 0 :=
    (panelSupportExtensor_ne_zero_iff n₁ n₂).mpr ((normalsJoin_ne_zero_iff n₁ n₂).mp hn₁₂)
  have hne₂₀ : panelSupportExtensor (k := k) n₂ n₀ ≠ 0 :=
    (panelSupportExtensor_ne_zero_iff n₂ n₀).mpr ((normalsJoin_ne_zero_iff n₂ n₀).mp hn₂₀)
  -- `G.endsOf` needs `Inhabited α`.
  haveI : Inhabited α := ⟨v⟩
  -- Build the seed `q₀`: vertex `v ↦ n₀`, `a ↦ n₁`, `b ↦ n₂`, junk elsewhere.
  let q₀ : α × Fin (k + 2) → ℝ :=
    fun p => if p.1 = v then n₀ p.2 else if p.1 = a then n₁ p.2 else if p.1 = b then n₂ p.2 else 0
  -- Normal evaluations: q₀ at the three vertices (pointwise, used below).
  have hq₀v : ∀ i, q₀ (v, i) = n₀ i := fun i => by simp [q₀]
  have hq₀a : ∀ i, q₀ (a, i) = n₁ i := fun i => by
    simp only [q₀]; split_ifs with h1
    · exact absurd h1 hav
    · rfl
  have hq₀b : ∀ i, q₀ (b, i) = n₂ i := fun i => by
    simp only [q₀]; split_ifs with h1 h2
    · exact absurd h1 hbv
    · exact absurd h2.symm hab
    · rfl
  -- Equalities of functions `Fin(k+2) → ℝ` at the three bodies (for support extensor rewriting).
  have hfn_v : (fun i => q₀ (v, i)) = n₀ := funext hq₀v
  have hfn_a : (fun i => q₀ (a, i)) = n₁ := funext hq₀a
  have hfn_b : (fun i => q₀ (b, i)) = n₂ := funext hq₀b
  set F := (PanelHingeFramework.ofNormals (k := k) G G.endsOf q₀).toBodyHinge with hFdef
  -- Raw support extensor formula for `F`.
  have hsupp_raw : ∀ e : β,
      F.supportExtensor e = panelSupportExtensor (fun i => q₀ ((G.endsOf e).1, i))
        (fun i => q₀ ((G.endsOf e).2, i)) := fun e => by
    simp only [hFdef, PanelHingeFramework.toBodyHinge_supportExtensor,
               PanelHingeFramework.ofNormals_ends, PanelHingeFramework.ofNormals_normal]
  -- Support extensor at `eₐ` (link `v-a`): either `panelSupportExtensor n₀ n₁` or its negative.
  have hsupp_ea : F.supportExtensor eₐ = panelSupportExtensor n₀ n₁ ∨
      F.supportExtensor eₐ = -panelSupportExtensor n₀ n₁ := by
    rcases G.endsOf_eq_or_swap hG_ea with heo | heo
    · exact Or.inl (by rw [hsupp_raw, heo, hfn_v, hfn_a])
    · exact Or.inr (by rw [hsupp_raw, heo, hfn_a, hfn_v, panelSupportExtensor_swap])
  -- Support extensor at `f` (link `a-b`): either `panelSupportExtensor n₁ n₂` or its negative.
  have hsupp_f : F.supportExtensor f = panelSupportExtensor n₁ n₂ ∨
      F.supportExtensor f = -panelSupportExtensor n₁ n₂ := by
    rcases G.endsOf_eq_or_swap hf with heo | heo
    · exact Or.inl (by rw [hsupp_raw, heo, hfn_a, hfn_b])
    · exact Or.inr (by rw [hsupp_raw, heo, hfn_b, hfn_a, panelSupportExtensor_swap])
  -- Support extensor at `e_b` (link `v-b`): either `panelSupportExtensor n₂ n₀` or its negative.
  -- The T3 cyclic family is `n₀n₁, n₁n₂, n₂n₀`; `v-b` gives `n₀n₂ = -(n₂n₀)` or `n₂n₀`.
  have hsupp_eb : F.supportExtensor e_b = panelSupportExtensor n₂ n₀ ∨
      F.supportExtensor e_b = -panelSupportExtensor n₂ n₀ := by
    rcases G.endsOf_eq_or_swap hG_eb with heo | heo
    · exact Or.inr (by rw [hsupp_raw, heo, hfn_v, hfn_b, panelSupportExtensor_swap])
    · exact Or.inl (by rw [hsupp_raw, heo, hfn_b, hfn_v])
  -- `hne`: every linking edge has nonzero support extensor.
  -- Use `hsupp_raw`, case-split on endpoint membership in V(G)={v,a,b}, apply pairwise nonzero.
  have hne : ∀ e, G.IsLink e (G.endsOf e).1 (G.endsOf e).2 →
      F.supportExtensor e ≠ 0 := by
    intro e hlink
    have hne12 : (G.endsOf e).1 ≠ (G.endsOf e).2 := G.endsOf_fst_ne_snd hlink.edge_mem
    have hmem1 : (G.endsOf e).1 ∈ V(G) := hlink.left_mem
    have hmem2 : (G.endsOf e).2 ∈ V(G) := hlink.right_mem
    rw [hVeq] at hmem1 hmem2
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem1 hmem2
    rw [hsupp_raw]
    -- Case-split on membership using named hypotheses, then rewrite via hfn_*.
    rcases hmem1 with h1 | h1 | h1 <;> rcases hmem2 with h2 | h2 | h2
    · exact absurd (h1.trans h2.symm) hne12
    · rw [show (fun i => q₀ ((G.endsOf e).1, i)) = n₀ from by rw [h1]; exact hfn_v,
          show (fun i => q₀ ((G.endsOf e).2, i)) = n₁ from by rw [h2]; exact hfn_a]
      exact hne₀₁
    · rw [show (fun i => q₀ ((G.endsOf e).1, i)) = n₀ from by rw [h1]; exact hfn_v,
          show (fun i => q₀ ((G.endsOf e).2, i)) = n₂ from by rw [h2]; exact hfn_b,
          panelSupportExtensor_swap]
      exact neg_ne_zero.mpr hne₂₀
    · rw [show (fun i => q₀ ((G.endsOf e).1, i)) = n₁ from by rw [h1]; exact hfn_a,
          show (fun i => q₀ ((G.endsOf e).2, i)) = n₀ from by rw [h2]; exact hfn_v,
          panelSupportExtensor_swap]
      exact neg_ne_zero.mpr hne₀₁
    · exact absurd (h1.trans h2.symm) hne12
    · rw [show (fun i => q₀ ((G.endsOf e).1, i)) = n₁ from by rw [h1]; exact hfn_a,
          show (fun i => q₀ ((G.endsOf e).2, i)) = n₂ from by rw [h2]; exact hfn_b]
      exact hne₁₂
    · rw [show (fun i => q₀ ((G.endsOf e).1, i)) = n₂ from by rw [h1]; exact hfn_b,
          show (fun i => q₀ ((G.endsOf e).2, i)) = n₀ from by rw [h2]; exact hfn_v]
      exact hne₂₀
    · rw [show (fun i => q₀ ((G.endsOf e).1, i)) = n₂ from by rw [h1]; exact hfn_b,
          show (fun i => q₀ ((G.endsOf e).2, i)) = n₁ from by rw [h2]; exact hfn_a,
          panelSupportExtensor_swap]
      exact neg_ne_zero.mpr hne₁₂
    · exact absurd (h1.trans h2.symm) hne12
  -- `hgen`: the three triangle-edge extensors are LI.
  -- Each is ± one member of the T3 cyclic family `![C₀,C₁,C₂]`; negation preserves LI via
  -- `LinearIndependent.units_smul_iff`: `w • v` is LI ↔ `v` is LI (w units).
  have hgen : LinearIndependent ℝ
      ![F.supportExtensor eₐ, F.supportExtensor f, F.supportExtensor e_b] := by
    -- Helper: `![-C₀, -C₁, -C₂]`-type sign flips preserve LI.
    have hLI_neg : ∀ (ε₀ ε₁ ε₂ : ℝˣ),
        LinearIndependent ℝ
          (fun i : Fin 3 =>
            ![ε₀ • panelSupportExtensor (k := k) n₀ n₁,
              ε₁ • panelSupportExtensor n₁ n₂,
              ε₂ • panelSupportExtensor n₂ n₀] i) := by
      intro ε₀ ε₁ ε₂
      have : (fun i : Fin 3 =>
            ![ε₀ • panelSupportExtensor (k := k) n₀ n₁,
              ε₁ • panelSupportExtensor n₁ n₂,
              ε₂ • panelSupportExtensor n₂ n₀] i) =
          (![ε₀, ε₁, ε₂]) • (![panelSupportExtensor (k := k) n₀ n₁,
              panelSupportExtensor n₁ n₂, panelSupportExtensor n₂ n₀]) := by
        funext i; fin_cases i <;> rfl
      rw [this]
      exact (LinearIndependent.units_smul_iff _ _).mpr hLI'
    rcases hsupp_ea with hea | hea <;> rcases hsupp_f with hf' | hf' <;>
        rcases hsupp_eb with heb | heb <;>
      rw [hea, hf', heb]
    · exact hLI'
    · have h := hLI_neg 1 1 (Units.mk0 (-1 : ℝ) (by norm_num))
      convert h using 1; funext i; fin_cases i <;> (first | rfl | simp)
    · have h := hLI_neg 1 (Units.mk0 (-1 : ℝ) (by norm_num)) 1
      convert h using 1; funext i; fin_cases i <;> (first | rfl | simp)
    · have h := hLI_neg 1 (Units.mk0 (-1 : ℝ) (by norm_num)) (Units.mk0 (-1 : ℝ) (by norm_num))
      convert h using 1; funext i; fin_cases i <;> (first | rfl | simp)
    · have h := hLI_neg (Units.mk0 (-1 : ℝ) (by norm_num)) 1 1
      convert h using 1; funext i; fin_cases i <;> (first | rfl | simp)
    · have h := hLI_neg (Units.mk0 (-1 : ℝ) (by norm_num)) 1 (Units.mk0 (-1 : ℝ) (by norm_num))
      convert h using 1; funext i; fin_cases i <;> (first | rfl | simp)
    · have h := hLI_neg (Units.mk0 (-1 : ℝ) (by norm_num)) (Units.mk0 (-1 : ℝ) (by norm_num)) 1
      convert h using 1; funext i; fin_cases i <;> (first | rfl | simp)
    · have h := hLI_neg (Units.mk0 (-1 : ℝ) (by norm_num)) (Units.mk0 (-1 : ℝ) (by norm_num))
            (Units.mk0 (-1 : ℝ) (by norm_num))
      convert h using 1
  -- T2: rigidity on `{v,a,b}` via `theorem_55_triangle`.
  have hFgraph : F.graph = G := by
    simp only [hFdef, PanelHingeFramework.toBodyHinge_graph, PanelHingeFramework.ofNormals_graph]
  have hrigVAB : F.IsInfinitesimallyRigidOn {v, a, b} :=
    BodyHingeFramework.theorem_55_triangle F hav.symm hab hbv.symm hgen
      (hFgraph ▸ hG_ea) (hFgraph ▸ hf) (hFgraph ▸ hG_eb.symm)
  -- T1 vertex-set pin + upgrade to generic motive.
  have hrig : F.IsInfinitesimallyRigidOn V(G) := by rwa [hVeq]
  exact PanelHingeFramework.hasGenericFullRankRealization_of_rigidOn_ofNormals G G.endsOf
    (fun e u w he => G.isLink_endsOf he.edge_mem) hne
    ⟨v, hG_ea.left_mem⟩ hrig n hG.1


/-- **The `d = 3` Case-III (`hsplit`) producer, `hsplitGP` callback shape**
(`lem:case-II-realization` / `lem:case-III`, the `theorem_55_generic.hsplitGP` branch at `k = 2`;
Katoh–Tanigawa 2011 §6.4.1,
Lemma 6.10, Phases 22g–22h). The conjecture's crux at `d = 3`, stated at the **generic-motive
callback interface** that `theorem_55_generic`'s `hsplitGP` premise threads (the R2 verdict (B),
`notes/Phase22-realization-design.md` §1.41(5)): the producer receives `hnoRigid`, `G.Simple`, and
the **full conditioned induction hypothesis** `hIH` (the `(G'.Simple → generic) ∧ bare` pair over
all smaller minimal `0`-dof-graphs, mirroring `hcontractGP`), **chooses its own adjacent degree-2
pair** via the `d = 3` chain dichotomy (§1.49(1), verdict (β)), and concludes the **generic** motive
`HasGenericFullRankRealization 2 G`. No split-vertex data is handed in — the producer re-selects
it, exactly as KT's Lemma 6.10 invokes Lemma 4.6 inside its own proof.

**Dichotomy spine (G4a).** On `|V(G)|`:

* `|V(G)| = 3` — the **triangle base** (T1–T4): `exists_adjacent_degree_two_pair` (G4a-i) picks an
  adjacent degree-2 pair `v–a` and `exists_splitOff_data_of_degree_eq_two` its two `v`-edges, so
  `hasGenericFullRankRealization_of_triangle` (T4) closes the generic motive on the triangle
  directly (KT never splits a `|V| = 3` graph — §1.46 finding 2).
* `|V(G)| ≥ 4` — the **chain arm**: `exists_chain_data_of_noRigid` (G4a-ii) extracts the full chain
  data `(v,a,b,c,eₐ,e_b,e_c)` with the two degree-2 closures; with a fresh `e₀ ∉ E(G)`,
  `splitOff_isMinimalKDof` makes the `v`-split `G_v^{ab}` a smaller minimal `0`-dof-graph
  (`splitOff_vertexSet_ncard_lt` for the measure drop); `splitOff_simple_of_noRigid_of_card` (R3,
  KT Lemma 6.7(ii)) discharges the split's simplicity at `4 ≤ |V(G)|`, so the IH's **GP `.1`
  conjunct** yields the **generic** `v`-split realization — the seed `q` whose `IsGeneralPosition`
  conjunct *is* the placement transversal `hgab` and whose `AlgebraicIndependent ℚ` conjunct feeds
  the triple-LI bridge (§1.41(2), §1.48(2); the bare `.2` conjunct provably cannot supply either —
  a rigid realization may have parallel panels). That generic `v`-split realization feeds the
  carried **candidate-placement core** `hcand`.

`hcand` is the single *explicit* hypothesis carrying the genuinely-hard remaining work, in the
established "carry the analytic crux as `h…`, keep the node red" idiom (Phase 21b): it consumes the
chosen chain data and the IH-derived **generic** `v`-split realization and yields
`HasGenericFullRankRealization 2 G` — internally its `M₁/M₂/M₃` dispatch arms end in the bare
realization of `G`, and the discharge composes the landed GAP-2 upgrade
`hasGenericFullRankRealization_of_rigidOn_ofNormals` onto the concrete candidate (§1.49(5)). The
§1.49(5) producer-assembly leaf discharges it (Leaf 2/3 + the G4c/G4d/G4e dispatch + the GAP-3
good-`t` choice); `G.Simple`, `hnoRigid`, and `hfresh` remain available to that leaf as
producer-level hypotheses. The dichotomy spine and the IH-at-`v`-split wiring built here are the
rest of the producer. -/
theorem PanelHingeFramework.case_III_hsplit_producer [DecidableEq β] [Finite α] [Finite β]
    {n : ℕ} (hD : 6 ≤ Graph.bodyBarDim n) (G : Graph α β)
    -- the `theorem_55_generic.hsplit` premise data (at `n`, `k = 2`)
    (hG : G.IsMinimalKDof n 0) (hV3 : 3 ≤ V(G).ncard)
    (hnoRigid : ∀ H : Graph α β, ¬ H.IsProperRigidSubgraph G n)
    (hsimple : G.Simple)
    (hIH : ∀ G' : Graph α β, G'.IsMinimalKDof n 0 → 2 ≤ V(G').ncard →
      V(G').ncard < V(G).ncard →
      (G'.Simple → PanelHingeFramework.HasGenericFullRankRealization 2 n G') ∧
        HasPanelRealization 2 n G')
    -- a fresh edge label for the chain arm's short-circuit `ab`-edge (the (β) reduction
    -- `minimal_kdof_reduction_full` does no splitting internally, so the producer owns it; the
    -- shape `minimal_kdof_reduction`'s `hfresh` carried, moved here at the (β) interface, §1.49(1))
    (hfresh : ∀ G' : Graph α β, ∃ e₀ : β, e₀ ∉ E(G'))
    -- the candidate-placement core (the still-unbuilt Leaf 2/3 + the `M₁/M₂/M₃` dispatch,
    -- §1.49(5)): given the chosen chain data, a fresh `e₀ ∉ E(G)`, and the IH-derived **generic**
    -- `v`-split realization (the seed `q` with `hgab`/alg-indep, §1.41(2)), it produces the
    -- generic realization of `G` (the bare candidate + the GAP-2 upgrade). The genuinely-hard
    -- residual is carried here in the "explicit `h…` crux" idiom (Phase 21b); the
    -- producer-assembly leaf (§1.49(5)) discharges it.
    (hcand : ∀ (v a b c : α) (eₐ e_b e_c e₀ : β),
      v ∈ V(G) → a ∈ V(G) → b ∈ V(G) → c ∈ V(G) →
      a ≠ v → b ≠ v → b ≠ a → c ≠ v → c ≠ a → b ≠ c →
      eₐ ≠ e_b → eₐ ≠ e_c →
      G.IsLink eₐ v a → G.IsLink e_b v b → G.IsLink e_c a c →
      (∀ e x, G.IsLink e v x → e = eₐ ∨ e = e_b) →
      (∀ e x, G.IsLink e a x → e = eₐ ∨ e = e_c) →
      e₀ ∉ E(G) →
      (G.splitOff v a b e₀).deficiency n = 0 →
      PanelHingeFramework.HasGenericFullRankRealization 2 n (G.splitOff v a b e₀) →
      PanelHingeFramework.HasGenericFullRankRealization 2 n G) :
    PanelHingeFramework.HasGenericFullRankRealization 2 n G := by
  classical
  have hD3 : 3 ≤ Graph.bodyBarDim n := by omega
  have hD2 : 2 ≤ Graph.bodyBarDim n := by omega
  have hD1 : 1 ≤ Graph.bodyBarDim n := by omega
  haveI := hsimple
  -- Dichotomy on `|V(G)|`: the triangle base (`= 3`) versus the chain arm (`≥ 4`).
  rcases eq_or_lt_of_le hV3 with hV3eq | hV4
  · -- **Triangle base (T1–T4).** Pick an adjacent degree-2 pair and its two `v`-edges; T4 closes
    -- the generic motive on the triangle directly.
    have hcard3 : V(G).ncard = 3 := hV3eq.symm
    obtain ⟨v, a, hvG, haG, hdegv, _, eₐ, hlea⟩ :=
      Graph.exists_adjacent_degree_two_pair hD hV3 hG hnoRigid
    have hav : a ≠ v := hlea.ne.symm
    obtain ⟨a', b, eₐ', e_b, ha'v, hbv, ha'G, hbG, heab', hlea', hleb, _⟩ :=
      Graph.exists_splitOff_data_of_degree_eq_two hD1 hG.1 hvG haG hav hdegv
    -- The splitOff data at `v` supplies two distinct `v`-edges `eₐ'`, `e_b` with distinct far
    -- endpoints `a'`, `b` (`a' ≠ v`, `b ≠ v`); T4 needs exactly two such edges to pin the triangle.
    exact PanelHingeFramework.hasGenericFullRankRealization_of_triangle (n := n) (k := 2)
      G hD3 (by norm_num) hG hcard3 hlea' hleb ha'v hbv heab'
  · -- **Chain arm (`|V(G)| ≥ 4`).** Extract the chain data, build the `v`-split (a smaller minimal
    -- `0`-dof-graph by `splitOff_isMinimalKDof`, simple by R3), pull its **generic** realization
    -- from the IH's GP `.1` conjunct, and feed `hcand`.
    have hV4' : 4 ≤ V(G).ncard := hV4
    obtain ⟨v, a, b, c, eₐ, e_b, e_c, hvG, haG, hbG, hcG, hav, hbv, hba, hcv, hca, hbc,
      heab, heac, hlea, hleb, hlec, hclv, hcla⟩ :=
      Graph.exists_chain_data_of_noRigid hD hV4' hG hnoRigid
    -- A fresh edge label `e₀ ∉ E(G)` for the short-circuit `ab`-edge of the `v`-split.
    obtain ⟨e₀, he₀⟩ := hfresh G
    -- The `v`-split is a smaller minimal `0`-dof-graph; the IH realizes it.
    have hGv : (G.splitOff v a b e₀).IsMinimalKDof n 0 :=
      Graph.splitOff_isMinimalKDof hD2 hV3 hav hbv haG hbG hvG heab hlea hleb hclv he₀ hG hnoRigid
    have hGvlt : V(G.splitOff v a b e₀).ncard < V(G).ncard :=
      Graph.splitOff_vertexSet_ncard_lt hvG
    -- `|V(G.splitOff)| = |V(G)| − 1 ≥ 2` (one vertex `v` removed from `|V(G)| ≥ 3`).
    have hGv2 : 2 ≤ V(G.splitOff v a b e₀).ncard := by
      rw [Graph.vertexSet_splitOff, Set.ncard_diff (by simpa using hvG) (Set.toFinite _),
        Set.ncard_singleton]
      omega
    -- … and simple (R3, KT Lemma 6.7(ii)): an `ab`-parallel pair in the split would close the
    -- triangle `G[{v,a,b}]`, a proper rigid subgraph at `4 ≤ |V(G)|`, contradicting `hnoRigid`.
    have hGvSimple : (G.splitOff v a b e₀).Simple :=
      Graph.splitOff_simple_of_noRigid_of_card hD3 heab hlea hleb hV4' hnoRigid
    -- The IH's GP `.1` conjunct: the generic `v`-split realization (the placement seed `q`, whose
    -- `IsGeneralPosition` conjunct is `hgab` and whose alg-indep conjunct feeds the triple-LI
    -- bridge — the data the bare `.2` conjunct cannot supply, §1.41(1)–(2)).
    have hsplitGP : PanelHingeFramework.HasGenericFullRankRealization 2 n (G.splitOff v a b e₀) :=
      (hIH _ hGv hGv2 hGvlt).1 hGvSimple
    exact hcand v a b c eₐ e_b e_c e₀ hvG haG hbG hcG hav hbv hba hcv hca hbc heab heac
      hlea hleb hlec hclv hcla he₀ hGv.1 hsplitGP


/-- The edge permutation `σ = Equiv.swap e_b e₀ * Equiv.swap e₁ e_c` of the `ρ = (av)` relabel is
an involution. The two transpositions have disjoint supports (`{e_b, e₀}` and `{e₁, e_c}` are
disjoint by the four distinctness facts), so each cancels: `σ ∘ σ = id`. The shared
σ-cancellation step in `ofNormals_relabel` and `rigidityRows_ofNormals_relabel`. -/
private theorem hσσ_relabel {β : Type*} [DecidableEq β] {e_b e_c e₀ e₁ : β}
    (hbe₁ : e_b ≠ e₁) (hbec : e_b ≠ e_c) (h₀e₁ : e₀ ≠ e₁) (h₀ec : e₀ ≠ e_c) (f : β) :
    (Equiv.swap e_b e₀ * Equiv.swap e₁ e_c) ((Equiv.swap e_b e₀ * Equiv.swap e₁ e_c) f) = f := by
  -- Pointwise: the two swaps act on disjoint pairs `{e_b, e₀}` and `{e₁, e_c}`.
  simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_def]
  split_ifs <;> simp_all

/-- **G4c-ii (fixed-seed form): the `ρ = (av)` relabel transports the concrete v-split `ofNormals`
data to the concrete a-split `ofNormals` data at the SAME seed `q₀ ∘ ρ`**
(`lem:splitOff-ofNormals-relabel`, KT 2011 eq. (6.31) framework side, Phase 22h).

This is the transport in the **producer's direction**: the induction hypothesis realizes the
`v`-split `G.splitOff v a b e₀` (`G_v^{ab}` in KT) concretely as `ofNormals (G.splitOff v a b e₀)
ends₀ q₀` with the four generic-realization conjuncts (general position, rigidity on `V(G)∖{v}`,
link-recording, `AlgebraicIndependent ℚ`), and the `M₃` arm of the Case-III producer needs the SAME
data on the `a`-split `G.splitOff a v c e₁` (`G_a^{vc}`) at the SAME seed transported by
`ρ = Equiv.swap a v` — *not* a fresh existential realization (an independent realization has a
different seed, hence different `λ`s and a different `r̂`, collapsing the eq.-(6.44) trichotomy;
KT §6.4.1, eqs. (6.31)/(6.44)). So the lemma is stated at the `ofNormals` level, naming the
relabelled construction explicitly with

* edge permutation `σ = Equiv.swap e_b e₀ * Equiv.swap e₁ e_c`,
* seed `qρ (x, i) := q₀ (ρ x, i)` (the original seed reindexed by `ρ`),
* selector `endsσρ e := (ρ (ends₀ (σ e)).1, ρ (ends₀ (σ e)).2)`,

so the producer and `G4d-ii` can name the relabelled framework `ofNormals (G.splitOff a v c e₁)
endsσρ qρ` directly (its row-space correspondence is `rigidityRows_ofNormals_relabel`, below).

The four conjuncts transport via the graph-level iso `G4c-i` (`Graph.splitOff_isLink_relabel`),
which `ρ`/`σ` intertwine. **GP:** `qρ`'s normals are `q₀`'s reindexed by the injective `ρ`.
**Rigidity:** a motion `S` of the `a`-split framework pulls back to the motion `S ∘ ρ` of the
`v`-split framework (using `splitOff_isLink_relabel` to move each `a`-split link to a `v`-split
link, and the support-extensor equality across the two `ofNormals` terms); the `v`-split rigidity
on `V(G)∖{v}` then forces `S` constant on `V(G)∖{a}` since `ρ` maps `V(G)∖{a} → V(G)∖{v}`
bijectively. **Link-recording:** each `a`-split link maps forward to a `v`-split link whose
endpoints `ends₀` records, transported through `ρ`. **AlgIndep:** `qρ` is an injective `ρ`-reindex
of `q₀`. -/
theorem PanelHingeFramework.ofNormals_relabel [DecidableEq α] [DecidableEq β]
    {G : Graph α β}
    {v a b c : α} {eₐ e_b e_c e₀ e₁ : β}
    (hG_ea : G.IsLink eₐ v a) (hG_eb : G.IsLink e_b v b) (hG_ec : G.IsLink e_c a c)
    (hav : a ≠ v) (hbv : b ≠ v) (hcv : c ≠ v) (hca : c ≠ a)
    (heab : eₐ ≠ e_b) (heac : eₐ ≠ e_c)
    (hclv : ∀ e x, G.IsLink e v x → e = eₐ ∨ e = e_b)
    (hcla : ∀ e x, G.IsLink e a x → e = eₐ ∨ e = e_c)
    (he₀ : e₀ ∉ E(G)) (he₁ : e₁ ∉ E(G)) (he₁₀ : e₁ ≠ e₀)
    {ends₀ : β → α × α} {q₀ : α × Fin (k + 2) → ℝ}
    (hQgp : (PanelHingeFramework.ofNormals (G.splitOff v a b e₀) ends₀ q₀).IsGeneralPosition)
    (hQrig :
      (PanelHingeFramework.ofNormals (G.splitOff v a b e₀) ends₀
        q₀).toBodyHinge.IsInfinitesimallyRigidOn V(G.splitOff v a b e₀))
    (hQrec : ∀ e u w, (G.splitOff v a b e₀).IsLink e u w →
        ends₀ e = (u, w) ∨ ends₀ e = (w, u))
    (hQalg : AlgebraicIndependent ℚ (fun p : α × Fin (k + 2) => q₀ (p.1, p.2))) :
    (PanelHingeFramework.ofNormals (G.splitOff a v c e₁)
        (fun e => (Equiv.swap a v (ends₀ ((Equiv.swap e_b e₀ * Equiv.swap e₁ e_c) e)).1,
          Equiv.swap a v (ends₀ ((Equiv.swap e_b e₀ * Equiv.swap e₁ e_c) e)).2))
        (fun p => q₀ (Equiv.swap a v p.1, p.2))).IsGeneralPosition ∧
    (PanelHingeFramework.ofNormals (G.splitOff a v c e₁)
        (fun e => (Equiv.swap a v (ends₀ ((Equiv.swap e_b e₀ * Equiv.swap e₁ e_c) e)).1,
          Equiv.swap a v (ends₀ ((Equiv.swap e_b e₀ * Equiv.swap e₁ e_c) e)).2))
        (fun p => q₀ (Equiv.swap a v p.1, p.2))).toBodyHinge.IsInfinitesimallyRigidOn
          V(G.splitOff a v c e₁) ∧
    (∀ e u w, (G.splitOff a v c e₁).IsLink e u w →
        (Equiv.swap a v (ends₀ ((Equiv.swap e_b e₀ * Equiv.swap e₁ e_c) e)).1,
          Equiv.swap a v (ends₀ ((Equiv.swap e_b e₀ * Equiv.swap e₁ e_c) e)).2) = (u, w) ∨
        (Equiv.swap a v (ends₀ ((Equiv.swap e_b e₀ * Equiv.swap e₁ e_c) e)).1,
          Equiv.swap a v (ends₀ ((Equiv.swap e_b e₀ * Equiv.swap e₁ e_c) e)).2) = (w, u)) ∧
    AlgebraicIndependent ℚ
      (fun p : α × Fin (k + 2) => q₀ (Equiv.swap a v p.1, p.2)) := by
  classical
  set ρ : Equiv.Perm α := Equiv.swap a v with hρ_def
  set σ : Equiv.Perm β := Equiv.swap e_b e₀ * Equiv.swap e₁ e_c with hσ_def
  set endsσρ : β → α × α := fun e => (ρ (ends₀ (σ e)).1, ρ (ends₀ (σ e)).2) with hendsσρ
  set qρ : α × Fin (k + 2) → ℝ := fun p => q₀ (ρ p.1, p.2) with hqρ
  -- ρ ∘ ρ = id.
  have hρρ : ∀ x : α, ρ (ρ x) = x := fun x => Equiv.swap_apply_self a v x
  -- ρ maps V(G) to itself (a, v ∈ V(G)).
  have hρmemV : ∀ u : α, u ∈ V(G) → ρ u ∈ V(G) := fun u hu => by
    rw [hρ_def, Equiv.swap_apply_def]
    split_ifs with h1 h2
    · exact hG_ea.left_mem   -- u = a → ρ u = v ∈ V(G)
    · exact hG_ea.right_mem  -- u = v → ρ u = a ∈ V(G)
    · exact hu               -- otherwise fixed
  -- ρ maps V(G) \ {a} to V(G) \ {v} bijectively.
  have hρ_diff : ∀ u : α, u ∈ V(G) \ {a} → ρ u ∈ V(G) \ {v} := fun u hu => by
    refine Set.mem_diff_of_mem (hρmemV u hu.1) ?_
    intro h
    have hρa : ρ a = v := by rw [hρ_def]; exact Equiv.swap_apply_left a v
    have hua : u = a := ρ.injective ((Set.mem_singleton_iff.mp h).trans hρa.symm)
    exact hu.2 (Set.mem_singleton_iff.mpr hua)
  -- σ ∘ σ = id, from the four edge-distinctness facts.
  have hbe₁ : e_b ≠ e₁ := fun h => he₁ (h ▸ hG_eb.edge_mem)
  have h₀ec : e₀ ≠ e_c := fun h => he₀ (h ▸ hG_ec.edge_mem)
  have hbec : e_b ≠ e_c := by
    intro h
    rcases hG_eb.left_eq_or_eq (h ▸ hG_ec) with h1 | h1
    · exact hav h1.symm
    · exact hcv h1.symm
  have hσσ : ∀ f, σ (σ f) = f := fun f => hσσ_relabel hbe₁ hbec he₁₀.symm h₀ec f
  set Q := PanelHingeFramework.ofNormals (G.splitOff v a b e₀) ends₀ q₀ with hQ_def
  set Q' := PanelHingeFramework.ofNormals (G.splitOff a v c e₁) endsσρ qρ with hQ'_def
  -- Q'.supportExtensor f = Q.supportExtensor (σ f): the relabelled framework's hinge at f reads
  -- q₀ at the ρ-shifted endpoints, i.e. the original hinge at (σ f). No σ-involution needed.
  have h_supp : ∀ f : β,
      Q'.toBodyHinge.supportExtensor f = Q.toBodyHinge.supportExtensor (σ f) := by
    intro f
    simp only [hQ_def, hQ'_def, PanelHingeFramework.toBodyHinge_supportExtensor,
      PanelHingeFramework.ofNormals_ends, PanelHingeFramework.ofNormals_normal, hendsσρ, hqρ, hρρ]
  refine ⟨?_, ?_, ?_, ?_⟩
  -- (1) General position: Q'.normal x = q₀ (ρ x, ·), reindexed by injective ρ.
  · intro x y hxy
    change LinearIndependent ℝ ![fun i => qρ (x, i), fun i => qρ (y, i)]
    have := hQgp (ρ x) (ρ y) (ρ.injective.ne hxy)
    simpa only [hQ_def, PanelHingeFramework.ofNormals_normal, hqρ] using this
  -- (2) Rigidity: any motion S of Q' yields the motion S ∘ ρ of Q, constant on V(G) \ {v},
  --     hence S constant on V(G) \ {a}.
  · intro S hS u hu w hw
    -- S ∘ ρ is an infinitesimal motion of Q.
    have hSmot : Q.toBodyHinge.IsInfinitesimalMotion (S ∘ ρ) := by
      intro f x y hf
      simp only [hQ_def, PanelHingeFramework.toBodyHinge_graph,
        PanelHingeFramework.ofNormals_graph] at hf
      have hfQ' : (G.splitOff a v c e₁).IsLink (σ f) (ρ x) (ρ y) :=
        (_root_.Graph.splitOff_isLink_relabel hG_ea hG_eb hG_ec hav hbv hcv hca
          heab heac hclv hcla he₀ he₁ he₁₀).mpr (by rw [hσσ f, hρρ, hρρ]; exact hf)
      have harg : Q'.toBodyHinge.graph.IsLink (σ f) (ρ x) (ρ y) := by
        simp only [hQ'_def, PanelHingeFramework.toBodyHinge_graph,
          PanelHingeFramework.ofNormals_graph]; exact hfQ'
      have hSc : Q'.toBodyHinge.hingeConstraint S (σ f) (ρ x) (ρ y) := hS (σ f) (ρ x) (ρ y) harg
      -- hSc : S (ρ x) - S (ρ y) ∈ span {Q'.supportExtensor (σ f)} = span {Q.supportExtensor f}.
      change (S ∘ ρ) x - (S ∘ ρ) y ∈ Submodule.span ℝ {Q.toBodyHinge.supportExtensor f}
      rw [show Q.toBodyHinge.supportExtensor f = Q'.toBodyHinge.supportExtensor (σ f) by
        rw [h_supp (σ f), hσσ f]]
      exact hSc
    -- Apply Q's rigidity on V(G.splitOff v a b e₀) = V(G) \ {v}.
    rw [Graph.vertexSet_splitOff] at hu hw
    have hρu := hρ_diff u hu
    have hρw := hρ_diff w hw
    rw [hQ_def, Graph.vertexSet_splitOff] at hQrig
    have hSmotConst := hQrig (S ∘ ρ) hSmot (ρ u) hρu (ρ w) hρw
    simp only [Function.comp] at hSmotConst
    rwa [hρρ u, hρρ w] at hSmotConst
  -- (3) Link-recording: every link of G.splitOff a v c e₁ has endpoints recorded by endsσρ.
  · intro e' u w he'
    have hfQ : (G.splitOff v a b e₀).IsLink (σ e') (ρ u) (ρ w) :=
      (_root_.Graph.splitOff_isLink_relabel hG_ea hG_eb hG_ec hav hbv hcv hca
        heab heac hclv hcla he₀ he₁ he₁₀).mp he'
    rcases hQrec (σ e') (ρ u) (ρ w) hfQ with h1 | h1
    · refine Or.inl ?_
      change (ρ (ends₀ (σ e')).1, ρ (ends₀ (σ e')).2) = (u, w)
      rw [h1]; exact Prod.ext (hρρ u) (hρρ w)
    · refine Or.inr ?_
      change (ρ (ends₀ (σ e')).1, ρ (ends₀ (σ e')).2) = (w, u)
      rw [h1]; exact Prod.ext (hρρ w) (hρρ u)
  -- (4) AlgebraicIndependent ℚ: qρ is an injective ρ-reindex of q₀.
  · change AlgebraicIndependent ℚ (fun p : α × Fin (k + 2) => q₀ (ρ p.1, p.2))
    have := hQalg.comp (fun p : α × Fin (k + 2) => (ρ p.1, p.2))
        (fun p q h => Prod.ext (ρ.injective (Prod.ext_iff.mp h).1) (Prod.ext_iff.mp h).2)
    simpa only [Function.comp] using this

/-- **G4c-ii (row-space correspondence): the relabelled `a`-split framework's rigidity rows are the
image of the `v`-split framework's under the dual of the `ρ`-coordinate permutation** (the
deliverable `G4d-ii` consumes; KT 2011 eqs. (6.31)/(6.44), Phase 22h).

The coordinate-relabel map `LinearMap.funLeft ℝ (ScrewSpace k) ρ : (α → ScrewSpace k) →ₗ[ℝ]
(α → ScrewSpace k)`, `S ↦ S ∘ ρ`, has dual `(funLeft ℝ _ ρ).dualMap` sending `φ ↦ φ ∘ (· ∘ ρ)`.
Under it, each rigidity row `hingeRow u w r` of the `a`-split framework `ofNormals (G.splitOff a v c
e₁) endsσρ qρ` is the image of the `v`-split framework's row `hingeRow (ρ u) (ρ w) r` — because
`ρ ∘ ρ = id`, `(funLeft ρ).dualMap (hingeRow (ρ u) (ρ w) r) = hingeRow u w r`. As `G4c-i`
(`Graph.splitOff_isLink_relabel`) puts the two graphs' links in `ρ`-correspondence and the
hinge-row blocks at corresponding edges coincide (the same support extensor, by the same `q₀`
reindex as in `ofNormals_relabel`), the two rigidity-row *sets* correspond exactly under
`(funLeft ρ).dualMap`. This is the row-space identity the eq.-(6.44) `M₃` candidate-row membership
step transports across. -/
theorem PanelHingeFramework.rigidityRows_ofNormals_relabel [DecidableEq α] [DecidableEq β]
    {G : Graph α β}
    {v a b c : α} {eₐ e_b e_c e₀ e₁ : β}
    (hG_ea : G.IsLink eₐ v a) (hG_eb : G.IsLink e_b v b) (hG_ec : G.IsLink e_c a c)
    (hav : a ≠ v) (hbv : b ≠ v) (hcv : c ≠ v) (hca : c ≠ a)
    (heab : eₐ ≠ e_b) (heac : eₐ ≠ e_c)
    (hclv : ∀ e x, G.IsLink e v x → e = eₐ ∨ e = e_b)
    (hcla : ∀ e x, G.IsLink e a x → e = eₐ ∨ e = e_c)
    (he₀ : e₀ ∉ E(G)) (he₁ : e₁ ∉ E(G)) (he₁₀ : e₁ ≠ e₀)
    (ends₀ : β → α × α) (q₀ : α × Fin (k + 2) → ℝ) :
    (PanelHingeFramework.ofNormals (G.splitOff a v c e₁)
        (fun e => (Equiv.swap a v (ends₀ ((Equiv.swap e_b e₀ * Equiv.swap e₁ e_c) e)).1,
          Equiv.swap a v (ends₀ ((Equiv.swap e_b e₀ * Equiv.swap e₁ e_c) e)).2))
        (fun p => q₀ (Equiv.swap a v p.1, p.2))).toBodyHinge.rigidityRows =
      (LinearMap.funLeft ℝ (ScrewSpace k) (Equiv.swap a v)).dualMap ''
        (PanelHingeFramework.ofNormals (G.splitOff v a b e₀) ends₀
          q₀).toBodyHinge.rigidityRows := by
  classical
  set ρ : Equiv.Perm α := Equiv.swap a v with hρ_def
  set σ : Equiv.Perm β := Equiv.swap e_b e₀ * Equiv.swap e₁ e_c with hσ_def
  set endsσρ : β → α × α := fun e => (ρ (ends₀ (σ e)).1, ρ (ends₀ (σ e)).2) with hendsσρ
  set qρ : α × Fin (k + 2) → ℝ := fun p => q₀ (ρ p.1, p.2) with hqρ
  have hρρ : ∀ x : α, ρ (ρ x) = x := fun x => Equiv.swap_apply_self a v x
  -- (funLeft ρ).dualMap (hingeRow (ρ u) (ρ w) r) = hingeRow u w r.
  have hdual : ∀ (u w : α) (r : Module.Dual ℝ (ScrewSpace k)),
      (LinearMap.funLeft ℝ (ScrewSpace k) ρ).dualMap
        (BodyHingeFramework.hingeRow (ρ u) (ρ w) r) = BodyHingeFramework.hingeRow u w r := by
    intro u w r
    refine LinearMap.ext fun S => ?_
    rw [LinearMap.dualMap_apply, BodyHingeFramework.hingeRow_apply,
      BodyHingeFramework.hingeRow_apply]
    simp only [LinearMap.funLeft_apply, hρρ]
  have hbe₁ : e_b ≠ e₁ := fun h => he₁ (h ▸ hG_eb.edge_mem)
  have h₀ec : e₀ ≠ e_c := fun h => he₀ (h ▸ hG_ec.edge_mem)
  have hbec : e_b ≠ e_c := by
    intro h
    rcases hG_eb.left_eq_or_eq (h ▸ hG_ec) with h1 | h1
    · exact hav h1.symm
    · exact hcv h1.symm
  have hσσ : ∀ f, σ (σ f) = f := fun f => hσσ_relabel hbe₁ hbec he₁₀.symm h₀ec f
  set Q := PanelHingeFramework.ofNormals (G.splitOff v a b e₀) ends₀ q₀ with hQ_def
  set Q' := PanelHingeFramework.ofNormals (G.splitOff a v c e₁) endsσρ qρ with hQ'_def
  -- Q'.supportExtensor f = Q.supportExtensor (σ f): the relabelled hinge at f reads q₀ at the
  -- ρ-shifted endpoints, i.e. the original hinge at (σ f). No σ-involution needed.
  have h_supp : ∀ f : β,
      Q'.toBodyHinge.supportExtensor f = Q.toBodyHinge.supportExtensor (σ f) := by
    intro f
    simp only [hQ_def, hQ'_def, PanelHingeFramework.toBodyHinge_supportExtensor,
      PanelHingeFramework.ofNormals_ends, PanelHingeFramework.ofNormals_normal, hendsσρ, hqρ, hρρ]
  -- The hinge-row blocks at ρ-corresponding edges coincide (dual annihilator of the same span).
  have hblock : ∀ f : β,
      Q'.toBodyHinge.hingeRowBlock f = Q.toBodyHinge.hingeRowBlock (σ f) := by
    intro f; simp only [BodyHingeFramework.hingeRowBlock, h_supp f]
  apply Set.eq_of_subset_of_subset
  -- ⊆ : every a-split row is the image of a matching v-split row.
  · rintro φ ⟨e', u, w, hlink', r, hr, rfl⟩
    refine ⟨BodyHingeFramework.hingeRow (ρ u) (ρ w) r,
      ⟨σ e', ρ u, ρ w, ?_, r, ?_, rfl⟩, hdual u w r⟩
    · have hmp := (_root_.Graph.splitOff_isLink_relabel hG_ea hG_eb hG_ec hav hbv hcv hca
        heab heac hclv hcla he₀ he₁ he₁₀ (e := e') (x := u) (y := w)).mp
      simp only [hQ'_def, PanelHingeFramework.toBodyHinge_graph,
        PanelHingeFramework.ofNormals_graph] at hlink'
      simpa only [hQ_def, PanelHingeFramework.toBodyHinge_graph,
        PanelHingeFramework.ofNormals_graph] using hmp hlink'
    · rw [← hblock e']; exact hr
  -- ⊇ : every image of a v-split row is an a-split row.
  · rintro φ ⟨ψ, ⟨e', u, w, hlink, r, hr, rfl⟩, rfl⟩
    refine ⟨σ e', ρ u, ρ w, ?_, r, ?_, ?_⟩
    · have hmpr := (_root_.Graph.splitOff_isLink_relabel hG_ea hG_eb hG_ec hav hbv hcv hca
        heab heac hclv hcla he₀ he₁ he₁₀ (e := σ e') (x := ρ u) (y := ρ w)).mpr
      simp only [hQ_def, PanelHingeFramework.toBodyHinge_graph,
        PanelHingeFramework.ofNormals_graph] at hlink
      simp only [hQ'_def, PanelHingeFramework.toBodyHinge_graph,
        PanelHingeFramework.ofNormals_graph]
      exact hmpr (by rw [hσσ e', hρρ, hρρ]; exact hlink)
    · rw [hblock (σ e'), hσσ e']; exact hr
    · have := hdual (ρ u) (ρ w) r
      rwa [hρρ, hρρ] at this

/-- **G4c-ii (existential corollary): the producer-direction transport at the level of the
existential motive** (`lem:splitOff-ofNormals-relabel`, KT 2011 eq. (6.31); Phase 22h). A short
consequence of the fixed-seed `ofNormals_relabel`: a generic full-rank realization of the `v`-split
`G.splitOff v a b e₀` (`G_v^{ab}`) transports to one of the `a`-split `G.splitOff a v c e₁`
(`G_a^{vc}`) at the relabelled seed `q₀ ∘ ρ`. This is the *producer's* direction (it consumes the
IH at the `v`-split, the form `theorem_55_generic`'s `hsplit` branch supplies, and yields the
`a`-split datum the `M₃` arm needs); the fixed-seed form above is the load-bearing one, since the
producer reads the concrete `ofNormals` framework and its row-space correspondence
(`rigidityRows_ofNormals_relabel`), not the bare existential. -/
theorem PanelHingeFramework.hasGenericFullRankRealization_of_splitOff_relabel [Finite α]
    {G : Graph α β}
    {v a b c : α} {eₐ e_b e_c e₀ e₁ : β}
    (hG_ea : G.IsLink eₐ v a) (hG_eb : G.IsLink e_b v b) (hG_ec : G.IsLink e_c a c)
    (hav : a ≠ v) (hbv : b ≠ v) (hcv : c ≠ v) (hca : c ≠ a)
    (heab : eₐ ≠ e_b) (heac : eₐ ≠ e_c)
    (hclv : ∀ e x, G.IsLink e v x → e = eₐ ∨ e = e_b)
    (hcla : ∀ e x, G.IsLink e a x → e = eₐ ∨ e = e_c)
    (he₀ : e₀ ∉ E(G)) (he₁ : e₁ ∉ E(G)) (he₁₀ : e₁ ≠ e₀)
    (n : ℕ) (hdef_in : (G.splitOff v a b e₀).deficiency n = 0)
    (hdef_out : (G.splitOff a v c e₁).deficiency n = 0)
    (hQ : PanelHingeFramework.HasGenericFullRankRealization k n (G.splitOff v a b e₀)) :
    PanelHingeFramework.HasGenericFullRankRealization k n (G.splitOff a v c e₁) := by
  classical
  obtain ⟨Q, hQg, hQgp, hQrank, hQrec, hQalg⟩ := hQ
  -- Derive rigidity from the rank hypothesis.
  have hne_in : V(G.splitOff v a b e₀).Nonempty :=
    ⟨a, by rw [Graph.vertexSet_splitOff]; exact ⟨hG_ea.right_mem, by simp [hav]⟩⟩
  have hne_in' : Q.toBodyHinge.graph.vertexSet.Nonempty := by
    rw [PanelHingeFramework.toBodyHinge_graph, hQg]; exact hne_in
  rw [hdef_in, sub_zero] at hQrank
  have hVeq_in : V(G.splitOff v a b e₀) = Q.toBodyHinge.graph.vertexSet := by
    rw [PanelHingeFramework.toBodyHinge_graph, hQg]
  have h1_in : 1 ≤ V(G.splitOff v a b e₀).ncard := (Set.ncard_pos (Set.toFinite _)).2 hne_in
  have hQrig : Q.toBodyHinge.IsInfinitesimallyRigidOn V(G.splitOff v a b e₀) := by
    rw [hVeq_in, BodyHingeFramework.isInfinitesimallyRigidOn_vertexSet_iff_finrank_span_rigidityRows
        Q.toBodyHinge hne_in', ← hVeq_in]
    zify [h1_in] at hQrank ⊢; exact_mod_cast hQrank
  -- Re-express Q as the canonical `ofNormals` of its own normals/ends; feed `ofNormals_relabel`.
  have hQeq : PanelHingeFramework.ofNormals (G.splitOff v a b e₀) Q.ends
      (fun p => Q.normal p.1 p.2) = Q := by rw [← hQg]; rfl
  have hgp' : (PanelHingeFramework.ofNormals (G.splitOff v a b e₀) Q.ends
      (fun p => Q.normal p.1 p.2)).IsGeneralPosition := by rw [hQeq]; exact hQgp
  have hrig' : (PanelHingeFramework.ofNormals (G.splitOff v a b e₀) Q.ends
      (fun p => Q.normal p.1 p.2)).toBodyHinge.IsInfinitesimallyRigidOn
        V(G.splitOff v a b e₀) := by rw [hQeq]; exact hQrig
  have hrec' : ∀ e u w, (G.splitOff v a b e₀).IsLink e u w →
      Q.ends e = (u, w) ∨ Q.ends e = (w, u) := by
    intro e u w he
    rcases hQrec e u w he with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl (Prod.ext h1 h2)
    · exact Or.inr (Prod.ext h1 h2)
  obtain ⟨hgp, hrig_out, hrec, halg⟩ := PanelHingeFramework.ofNormals_relabel hG_ea hG_eb hG_ec
    hav hbv hcv hca heab heac hclv hcla he₀ he₁ he₁₀ hgp' hrig' hrec' hQalg
  -- Derive rank from the rigidity of the output framework.
  set F_out := PanelHingeFramework.ofNormals (G.splitOff a v c e₁)
      (fun e => (Equiv.swap a v (Q.ends ((Equiv.swap e_b e₀ * Equiv.swap e₁ e_c) e)).1,
        Equiv.swap a v (Q.ends ((Equiv.swap e_b e₀ * Equiv.swap e₁ e_c) e)).2))
      (fun p => Q.normal (Equiv.swap a v p.1) p.2) with hF_out
  have hne_out : V(G.splitOff a v c e₁).Nonempty :=
    ⟨c, by rw [Graph.vertexSet_splitOff]; exact ⟨hG_ec.right_mem, by simp [hca]⟩⟩
  have h1_out : 1 ≤ V(G.splitOff a v c e₁).ncard := (Set.ncard_pos (Set.toFinite _)).2 hne_out
  have hW2 := F_out.toBodyHinge.finrank_span_rigidityRows_of_rigidOn hne_out
    (by rw [PanelHingeFramework.toBodyHinge_graph,
        PanelHingeFramework.ofNormals_graph]; exact hrig_out)
  have hrank_out :
      (Module.finrank ℝ (Submodule.span ℝ F_out.toBodyHinge.rigidityRows) : ℤ) =
      screwDim k * ((V(G.splitOff a v c e₁).ncard : ℤ) - 1) -
      (G.splitOff a v c e₁).deficiency n := by
    rw [hdef_out, sub_zero]
    have hVncard_out : F_out.toBodyHinge.graph.vertexSet.ncard = V(G.splitOff a v c e₁).ncard := by
      rw [PanelHingeFramework.toBodyHinge_graph, PanelHingeFramework.ofNormals_graph]
    rw [← hVncard_out]
    rw [← hVncard_out] at h1_out
    zify [h1_out] at hW2 ⊢; exact_mod_cast hW2
  -- Repackage the link conjunct from Prod-equality form into the motive's And/Or form.
  refine ⟨_, rfl, hgp, hrank_out, fun e u w he => ?_, halg⟩
  rcases hrec e u w he with h1 | h1
  · exact Or.inl ⟨by rw [PanelHingeFramework.ofNormals_ends, (Prod.ext_iff.mp h1).1],
      by rw [PanelHingeFramework.ofNormals_ends, (Prod.ext_iff.mp h1).2]⟩
  · exact Or.inr ⟨by rw [PanelHingeFramework.ofNormals_ends, (Prod.ext_iff.mp h1).1],
      by rw [PanelHingeFramework.ofNormals_ends, (Prod.ext_iff.mp h1).2]⟩

/-- **G4c-ii (membership transport): a `v`-split rigidity-row-span member transports to the
relabelled `a`-split rigidity-row span under the dual of the `ρ`-coordinate permutation**
(`lem:splitOff-rigidityRows-relabel`, the membership corollary of `rigidityRows_ofNormals_relabel`;
KT 2011 eqs.~(6.31)/(6.44), Phase 22h). The `M₃` arm of the Case-III producer reads its candidate
row off the `v`-split framework `R(G_v^{ab}, q)` (G4d-ii gives `hingeRow a c r̂ ∈ span` there), but
the `a`-split realization it actually places is `ofNormals (G.splitOff a v c e₁) endsσρ qρ`. This is
the transport across the relabel: since the two frameworks' rigidity-row *sets* correspond exactly
under `(funLeft ρ).dualMap` (`rigidityRows_ofNormals_relabel`), the span of one is the
`Submodule.map`-image of the span of the other (`Submodule.span_image`), so any `φ` in the `v`-split
span sends to `(funLeft ρ).dualMap φ` in the `a`-split span (`Submodule.mem_map_of_mem`). Composed
with `hingeRow_funLeft_dualMap` (which evaluates `(funLeft ρ).dualMap (hingeRow u w r) =
hingeRow (ρ u) (ρ w) r` for the involution `ρ = (a v)`), this is exactly the `M₃` candidate-row
membership the arm needs: `hingeRow a c r̂ ∈ span(v-split) ↦ hingeRow v c r̂ ∈ span(a-split)`
(`ρ a = v`, `ρ c = c`). Graph-free over the carrier beyond the relabel lemma it invokes. -/
theorem PanelHingeFramework.mem_span_rigidityRows_ofNormals_relabel [DecidableEq α] [DecidableEq β]
    {G : Graph α β}
    {v a b c : α} {eₐ e_b e_c e₀ e₁ : β}
    (hG_ea : G.IsLink eₐ v a) (hG_eb : G.IsLink e_b v b) (hG_ec : G.IsLink e_c a c)
    (hav : a ≠ v) (hbv : b ≠ v) (hcv : c ≠ v) (hca : c ≠ a)
    (heab : eₐ ≠ e_b) (heac : eₐ ≠ e_c)
    (hclv : ∀ e x, G.IsLink e v x → e = eₐ ∨ e = e_b)
    (hcla : ∀ e x, G.IsLink e a x → e = eₐ ∨ e = e_c)
    (he₀ : e₀ ∉ E(G)) (he₁ : e₁ ∉ E(G)) (he₁₀ : e₁ ≠ e₀)
    (ends₀ : β → α × α) (q₀ : α × Fin (k + 2) → ℝ)
    {φ : Module.Dual ℝ (α → ScrewSpace k)}
    (hφ : φ ∈ Submodule.span ℝ
      (PanelHingeFramework.ofNormals (G.splitOff v a b e₀) ends₀ q₀).toBodyHinge.rigidityRows) :
    (LinearMap.funLeft ℝ (ScrewSpace k) (Equiv.swap a v)).dualMap φ ∈ Submodule.span ℝ
      (PanelHingeFramework.ofNormals (G.splitOff a v c e₁)
        (fun e => (Equiv.swap a v (ends₀ ((Equiv.swap e_b e₀ * Equiv.swap e₁ e_c) e)).1,
          Equiv.swap a v (ends₀ ((Equiv.swap e_b e₀ * Equiv.swap e₁ e_c) e)).2))
        (fun p => q₀ (Equiv.swap a v p.1, p.2))).toBodyHinge.rigidityRows := by
  rw [PanelHingeFramework.rigidityRows_ofNormals_relabel hG_ea hG_eb hG_ec hav hbv hcv hca
      heab heac hclv hcla he₀ he₁ he₁₀ ends₀ q₀, Submodule.span_image]
  exact Submodule.mem_map_of_mem hφ

/-- **W9a — the short-circuit-free relabel transport** (the `M₃` candidate/bottom-row span-induction
core, design §1.52(b); Katoh–Tanigawa 2011 §6.4.1 eqs.~(6.31)/(6.39), Phase 22h). The G4d-i sibling
that transports a vector in the span of the `v`-split framework `Fv`'s rigidity rows across the
vertex relabel `(a v)` *with the `e_c`-content stripped*: for any `φ ∈ span Fv.rigidityRows`,
$$(\mathrm{funLeft}\,(a\,v)).\mathrm{dualMap}\,\varphi
\;-\; \mathrm{hingeRow}\;v\;c\;(\varphi\circ\mathrm{single}\,a)
\;\in\; \mathrm{span}\;F_{va}.\mathrm{rigidityRows},$$
where `Fva` is a second framework (concretely the `G − a` framework) whose links and hinge-row
blocks agree with `Fv` off body `a` (`htrans`).

This is the relabel half of KT's eq.~(6.39) row correspondence read functional-wise. Under the
degree-2-at-`a` hypothesis (the only `Fv`-links touching `a` are `e_c = ac`), the relabel
`(funLeft (a v)).dualMap` of a generator `hingeRow x y r` lands in the target row span after the
subtracted `a`-column hinge row cancels the `e_c`-content: a generator at `e_c` (endpoint `a`) maps
to `hingeRow v c r`, which the subtracted `hingeRow v c (φ ∘ single a) = hingeRow v c (±r)` exactly
cancels; an off-`a` generator is fixed by the swap (its endpoints avoid both `a` and `v`) and
survives into `Fva`'s rows via `htrans`. The candidate-functional `hρGv`-slot of the `M₃` arm (W9c)
reads this at `φ := hingeRow a b ρ`. Unlike the superseded `mem_span_rigidityRows_ofNormals_relabel`
(whose `a`-split span target cannot strip the short-circuit `e₁`-block post hoc), this concludes
directly in the `G − a`-row span. Graph-free over the carrier (`rigidityRows`/`hingeRowBlock` read
only `graph`/`hingeRowBlock`), so the `ofNormals` defeq trap (TACTICS-QUIRKS §38) does not bite. -/
theorem BodyHingeFramework.funLeft_dualMap_sub_acolumn_mem_span_rigidityRows
    [DecidableEq α] {Fv Fva : BodyHingeFramework k α β}
    {v a c : α} {e_c : β}
    (hca : c ≠ a) (hcv : c ≠ v)
    (hlink_ec : Fv.graph.IsLink e_c a c)
    (hdeg2 : ∀ f x, Fv.graph.IsLink f a x → f = e_c)
    (hdeg2r : ∀ f x, Fv.graph.IsLink f x a → f = e_c)
    (hnov : ∀ f x y, Fv.graph.IsLink f x y → x ≠ v ∧ y ≠ v)
    (htrans : ∀ f x y, Fv.graph.IsLink f x y → x ≠ a → y ≠ a →
      Fva.graph.IsLink f x y ∧ Fv.hingeRowBlock f ≤ Fva.hingeRowBlock f)
    {φ : Module.Dual ℝ (α → ScrewSpace k)}
    (hφ : φ ∈ Submodule.span ℝ Fv.rigidityRows) :
    (LinearMap.funLeft ℝ (ScrewSpace k) (Equiv.swap a v)).dualMap φ
        - BodyHingeFramework.hingeRow (k := k) (α := α) v c
            (φ.comp (LinearMap.single ℝ (fun _ : α => ScrewSpace k) a))
      ∈ Submodule.span ℝ Fva.rigidityRows := by
  -- Bundle the transport as a single linear map `T` so the `span_induction` predicate stays
  -- light (`T ψ ∈ span …`) — keeping the heavy `Module.Dual (α → ScrewSpace k)` terms out of
  -- the predicate, which is what the `add`/`smul`/`zero` cases discharge mechanically by
  -- `map_add`/`map_smul`/`map_zero`. `hingeRow v c (· ∘ single a)` is the linear composite
  -- `(screwDiff v c).dualMap ∘ₗ (single a).dualMap` (both `hingeRow_eq_dualMap` and
  -- `LinearMap.dualMap` of `single` unfold `∘ₗ` to the same `comp`).
  set T : Module.Dual ℝ (α → ScrewSpace k) →ₗ[ℝ] Module.Dual ℝ (α → ScrewSpace k) :=
    (LinearMap.funLeft ℝ (ScrewSpace k) (Equiv.swap a v)).dualMap
      - (screwDiff (k := k) (α := α) v c).dualMap.comp
          (LinearMap.single ℝ (fun _ : α => ScrewSpace k) a).dualMap with hT
  -- `T ψ` is the transported difference, for every `ψ` (the `hingeRow`/`comp` forms agree with
  -- the `dualMap` composites by `rfl`).
  have hTapply : ∀ ψ : Module.Dual ℝ (α → ScrewSpace k),
      T ψ = (LinearMap.funLeft ℝ (ScrewSpace k) (Equiv.swap a v)).dualMap ψ
        - BodyHingeFramework.hingeRow (k := k) (α := α) v c
            (ψ.comp (LinearMap.single ℝ (fun _ : α => ScrewSpace k) a)) := fun ψ => by
    rw [hT, LinearMap.sub_apply, LinearMap.comp_apply, hingeRow_eq_dualMap]; rfl
  rw [← hTapply]
  -- `span_induction` on `hφ` with the light predicate `T ψ ∈ span Fva.rigidityRows`.
  apply Submodule.span_induction
    (p := fun ψ _ => T ψ ∈ Submodule.span ℝ Fva.rigidityRows) _ _ _ _ hφ
  · -- generator case: ψ = hingeRow x y r at a link f, r ∈ Fv.hingeRowBlock f.
    -- Unfold `T` to the `dualMap` form (not via `hTapply`): keeping the subtracted term as
    -- `(screwDiff v c).dualMap (…)` lets `map_zero` close the off-case without producing the
    -- heavy nested `hingeRow v c 0` term whose `rw`-motive abstraction trips §38.
    rintro ψ ⟨f, x, y, hlink, r, hr, rfl⟩
    rw [hT, LinearMap.sub_apply, LinearMap.comp_apply,
      BodyHingeFramework.hingeRow_funLeft_dualMap,
      show (LinearMap.single ℝ (fun _ : α => ScrewSpace k) a).dualMap (hingeRow x y r)
          = (hingeRow x y r).comp (LinearMap.single ℝ (fun _ : α => ScrewSpace k) a) from rfl]
    by_cases hxa : x = a
    · -- x = a: hdeg2 forces f = e_c, hence y = c; the relabel is hingeRow v c r and the
      -- a-column is r, so the difference vanishes.
      have hfe : f = e_c := by rw [hxa] at hlink; exact hdeg2 f y hlink
      have hyc : y = c := by
        rw [hxa, hfe] at hlink
        rcases hlink.eq_and_eq_or_eq_and_eq hlink_ec with ⟨-, h⟩ | ⟨h, -⟩
        · exact h
        · exact absurd h (Ne.symm hca)
      rw [hxa, hyc]
      simp only [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hca hcv,
        hingeRow_comp_single_tail hca.symm, ← hingeRow_eq_dualMap, sub_self]
      exact Submodule.zero_mem _
    · by_cases hya : y = a
      · -- y = a, x ≠ a: hdeg2r forces f = e_c, hence x = c.
        have hfe : f = e_c := by rw [hya] at hlink; exact hdeg2r f x hlink
        have hxc : x = c := by
          rw [hya, hfe] at hlink
          rcases hlink.eq_and_eq_or_eq_and_eq hlink_ec with ⟨h, -⟩ | ⟨h, -⟩
          · exact absurd h hxa
          · exact h
        -- relabel: hingeRow c v r; a-column: hingeRow c a r ∘ single a = -r (swap then tail);
        -- subtracted row hingeRow v c (-r) = hingeRow c v r, so the difference vanishes.
        rw [hxc, hya]
        simp only [Equiv.swap_apply_of_ne_of_ne hca hcv, Equiv.swap_apply_left,
          hingeRow_swap c a r, hingeRow_comp_single_tail hca.symm, ← hingeRow_eq_dualMap,
          hingeRow_swap v c (-r), neg_neg, sub_self]
        exact Submodule.zero_mem _
      · -- x ≠ a, y ≠ a: the swap fixes both endpoints (they also avoid v by hnov), the a-column
        -- is 0, so the result is the generator itself — a genuine Fva-row via htrans.
        obtain ⟨hxv, hyv⟩ := hnov f x y hlink
        obtain ⟨hlink', hble⟩ := htrans f x y hlink hxa hya
        simp only [Equiv.swap_apply_of_ne_of_ne hxa hxv, Equiv.swap_apply_of_ne_of_ne hya hyv,
          hingeRow_comp_single_off (Ne.symm hxa) (Ne.symm hya), map_zero, sub_zero]
        exact Submodule.subset_span ⟨f, x, y, hlink', r, hble hr, rfl⟩
  · -- zero
    rw [map_zero]; exact Submodule.zero_mem _
  · -- add: `T` is linear, so the (x+y)-row is the sum of the x- and y-rows.
    intro x y _ _ hx hy
    rw [map_add]; exact Submodule.add_mem _ hx hy
  · -- smul
    intro t x _ hx
    rw [map_smul]; exact Submodule.smul_mem _ t hx

/-- **W9b — the `M₃` bottom-row tag transport** (the per-member relabel of one W6b bottom-family
member, design §1.52(c); Katoh–Tanigawa 2011 §6.4.1 eqs.~(6.39)/(6.41), Phase 22h). One bottom row
`φ` of the v-split W6b package — tagged either a genuine `R(G_v, q)`-row or an `(ab)`-block row
`hingeRow a b ρ'` (`ρ' ⊥ C(q(ab))`) — relabels under `(funLeft (a v)).dualMap` to a row tagged in
the `M₃`-arm shape: either a genuine row of the `G − a` framework at the overridden selector `ends₃`
and the relabeled seed `qρ = q ∘ (a v)`, or a `(c, v)`-block row `hingeRow c v ρ'`
(`ρ' ⊥ C(q(ac))`). This is exactly KT's eq.~(6.39) row correspondence `(vb)_j ↔ (ab)_j`,
`(va)_j ↔ (ac)_j`, `e_j ↔ e_j` read row-wise: the `(ab)`-block row maps to the genuine `e_b`-row of
`G − a` (`ends₃ e_b = (v, b)`, `qρ(v,·) = n_a`, `qρ(b,·) = n_b`); a `G_v`-row at the degree-2 body
`a`'s only edge `e_c = ac` maps to the candidate-shaped `(c, v)`-block row; every other `G_v`-row is
fixed by the swap and survives as a genuine `G − a`-row.

W9c maps this over the bottom family `w` to feed `case_III_arm_realization`'s `hwmem` slot at the
`M₃` roles. **§38:** every membership is built from an explicit link witness (the `hrow_mem` idiom)
and every extensor evaluation goes through `toBodyHinge_supportExtensor`/`ofNormals_ends`/
`ofNormals_normal` plus the `Equiv.swap` evaluation lemmas — never `whnf` on the `ofNormals`
carrier. -/
theorem PanelHingeFramework.case_III_bottom_relabel
    [DecidableEq α] {G Gv : Graph α β} {ends₀ ends₃ : β → α × α}
    {q : α × Fin (k + 2) → ℝ}
    {v a b c : α} {e_a e_b e_c : β}
    (hva : v ≠ a) (hab : a ≠ b) (hvb : v ≠ b) (hca : c ≠ a) (hcv : c ≠ v)
    (hG_ea : G.IsLink e_a v a) (hG_eb : G.IsLink e_b v b) (hG_ec : G.IsLink e_c a c)
    (hcla : ∀ e x, G.IsLink e a x → e = e_a ∨ e = e_c)
    (hGv_le : ∀ e x y, Gv.IsLink e x y → G.IsLink e x y)
    (hnov : ∀ e x y, Gv.IsLink e x y → x ≠ v ∧ y ≠ v)
    (hrecGv : ∀ e x y, Gv.IsLink e x y → ends₀ e = (x, y) ∨ ends₀ e = (y, x))
    (hends₃_eb : ends₃ e_b = (v, b))
    (hends₃_off : ∀ e, e ≠ e_a → e ≠ e_b → e ≠ e_c → ends₃ e = ends₀ e)
    {φ : Module.Dual ℝ (α → ScrewSpace k)}
    (hφ : φ ∈ (PanelHingeFramework.ofNormals Gv ends₀ q).toBodyHinge.rigidityRows ∨
      ∃ ρ' : Module.Dual ℝ (ScrewSpace k),
        ρ' (panelSupportExtensor (fun i => q (a, i)) (fun i => q (b, i))) = 0 ∧
        φ = BodyHingeFramework.hingeRow a b ρ') :
    (LinearMap.funLeft ℝ (ScrewSpace k) (Equiv.swap a v)).dualMap φ ∈
      (PanelHingeFramework.ofNormals (G.removeVertex a) ends₃
        (fun p => q (Equiv.swap a v p.1, p.2))).toBodyHinge.rigidityRows ∨
      ∃ ρ' : Module.Dual ℝ (ScrewSpace k),
        ρ' (panelSupportExtensor (fun i => q (c, i)) (fun i => q (a, i))) = 0 ∧
        (LinearMap.funLeft ℝ (ScrewSpace k) (Equiv.swap a v)).dualMap φ
          = BodyHingeFramework.hingeRow c v ρ' := by
  classical
  set qρ : α × Fin (k + 2) → ℝ := fun p => q (Equiv.swap a v p.1, p.2) with hqρ
  set Fv := (PanelHingeFramework.ofNormals Gv ends₀ q).toBodyHinge with hFv
  set Fva := (PanelHingeFramework.ofNormals (G.removeVertex a) ends₃ qρ).toBodyHinge with hFva
  -- The relabeled seed at body `x` reads `q` at the swapped body: `qρ(x,·) = q(swap a v x, ·)`.
  rcases hφ with hgen | ⟨ρ', hρ'e₀, rfl⟩
  · -- The `G_v`-row tag: destructure the generator and case on `a ∈ {x, y}`.
    obtain ⟨f, x, y, hlink, r, hr, rfl⟩ := hgen
    rw [hFv, PanelHingeFramework.toBodyHinge_graph, PanelHingeFramework.ofNormals_graph] at hlink
    rw [BodyHingeFramework.hingeRow_funLeft_dualMap]
    obtain ⟨hxv, hyv⟩ := hnov f x y hlink
    have hGflink := hGv_le f x y hlink
    -- `r`'s annihilation at `Fv`'s `f`-extensor (the `q`-seed at `ends₀ f`).
    have hr' : r (Fv.supportExtensor f) = 0 := (Fv.mem_hingeRowBlock_iff f r).1 hr
    rw [hFv, PanelHingeFramework.toBodyHinge_supportExtensor, PanelHingeFramework.ofNormals_normal,
      PanelHingeFramework.ofNormals_normal, PanelHingeFramework.ofNormals_ends] at hr'
    by_cases hxa : x = a
    · -- x = a: `hcla` forces `f = e_c` (the `e_a` branch links `v`, contradiction), then `y = c`.
      -- `subst x` (eliminate the local `x`, keeping the section body `a` / `c`).
      subst x
      have hfe : f = e_c := by
        rcases hcla f y hGflink with rfl | rfl
        · -- f = e_a: G.IsLink e_a a y and G.IsLink e_a v a, but a ≠ v (hva) and y ≠ v (hyv).
          rcases hG_ea.eq_and_eq_or_eq_and_eq hGflink with ⟨h1, _⟩ | ⟨h1, _⟩
          · exact absurd h1 hva
          · exact absurd h1.symm hyv
        · rfl
      -- `c = y` (flip so `subst` eliminates `y`, keeping the section variable `c`).
      have hcy : c = y := by
        rw [hfe] at hGflink
        rcases hG_ec.eq_and_eq_or_eq_and_eq hGflink with ⟨_, h2⟩ | ⟨_, h2⟩
        · exact h2
        · exact absurd h2 hca
      subst hcy
      -- relabel `hingeRow a c r → hingeRow v c r = hingeRow c v (-r)`; tag RIGHT with `ρ' := -r`.
      refine Or.inr ⟨-r, ?_, ?_⟩
      · -- annihilation: `r ⊥ C(q(ends₀ e_c))`, and `ends₀ e_c ∈ {(a,c),(c,a)}` (hrecGv).
        rw [hfe] at hr' hlink
        rw [LinearMap.neg_apply, neg_eq_zero]
        rcases hrecGv e_c a c hlink with he | he
        · rw [he] at hr'; rw [panelSupportExtensor_swap, map_neg, hr', neg_zero]
        · rw [he] at hr'; exact hr'
      · rw [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hca hcv]
        exact BodyHingeFramework.hingeRow_swap v c r
    · by_cases hya : y = a
      · -- y = a, x ≠ a: `hcla` forces `f = e_c`, then `x = c`.
        subst y
        have hfe : f = e_c := by
          rcases hcla f x hGflink.symm with rfl | rfl
          · rcases hG_ea.eq_and_eq_or_eq_and_eq hGflink with ⟨h1, _⟩ | ⟨h1, _⟩
            · exact absurd h1.symm hxv
            · exact absurd h1 hva
          · rfl
        have hcx : c = x := by
          rw [hfe] at hGflink
          rcases hG_ec.eq_and_eq_or_eq_and_eq hGflink with ⟨_, h2⟩ | ⟨_, h2⟩
          · exact absurd h2 hca
          · exact h2
        subst hcx
        -- relabel `hingeRow c a r → hingeRow c v r`; tag RIGHT with `ρ' := r`.
        refine Or.inr ⟨r, ?_, ?_⟩
        · rw [hfe] at hr' hlink
          rcases hrecGv e_c c a hlink with he | he
          · rw [he] at hr'; exact hr'
          · rw [he] at hr'; rw [panelSupportExtensor_swap, map_neg, hr', neg_zero]
        · rw [Equiv.swap_apply_of_ne_of_ne hca hcv, Equiv.swap_apply_left]
      · -- x ≠ a, y ≠ a: the swap fixes both endpoints; the image is the generator itself, a
        -- genuine `G − a`-row at the overridden selector `ends₃`.
        rw [Equiv.swap_apply_of_ne_of_ne hxa hxv, Equiv.swap_apply_of_ne_of_ne hya hyv]
        -- the image `hingeRow x y r` is a genuine row of `Fva`: the link survives `removeVertex a`
        -- and the `f`-extensor at `Fva` equals the `Fv`-extensor `r` annihilates.
        refine Or.inl ⟨f, x, y, ?_, r, ?_, rfl⟩
        · -- the link survives `removeVertex a` (endpoints `≠ a`).
          rw [hFva, PanelHingeFramework.toBodyHinge_graph, PanelHingeFramework.ofNormals_graph,
            Graph.removeVertex_isLink]
          exact ⟨hGflink, hxa, hya⟩
        · -- block: the `f`-extensor at `Fva` equals the `f`-extensor at `Fv` (off `{e_a,e_b,e_c}`,
          -- `ends₃ f = ends₀ f`, and the swap fixes the recorded endpoints `∉ {a, v}`).
          have hfne_a : f ≠ e_a := by
            rintro rfl
            rcases hG_ea.eq_and_eq_or_eq_and_eq hGflink with ⟨hh, _⟩ | ⟨hh, _⟩
            · exact hxv hh.symm
            · exact hyv hh.symm
          have hfne_b : f ≠ e_b := by
            rintro rfl
            rcases hG_eb.eq_and_eq_or_eq_and_eq hGflink with ⟨hh, _⟩ | ⟨hh, _⟩
            · exact hxv hh.symm
            · exact hyv hh.symm
          have hfne_c : f ≠ e_c := by
            rintro rfl
            rcases hG_ec.eq_and_eq_or_eq_and_eq hGflink with ⟨hh, _⟩ | ⟨hh, _⟩
            · exact hxa hh.symm
            · exact hya hh.symm
          rw [BodyHingeFramework.mem_hingeRowBlock_iff, hFva,
            PanelHingeFramework.toBodyHinge_supportExtensor, PanelHingeFramework.ofNormals_normal,
            PanelHingeFramework.ofNormals_normal, PanelHingeFramework.ofNormals_ends,
            hends₃_off f hfne_a hfne_b hfne_c]
          -- `ends₀ f ∈ {(x,y),(y,x)}` (hrecGv); the swap fixes `x, y ∉ {a, v}`, so `qρ = q` and
          -- the `Fva`-extensor matches the `Fv`-extensor `r` annihilates (`hr'`).
          rcases hrecGv f x y hlink with he | he <;> rw [he] at hr' ⊢ <;>
            simp only [hqρ, Equiv.swap_apply_of_ne_of_ne hxa hxv,
              Equiv.swap_apply_of_ne_of_ne hya hyv] <;> exact hr'
  · -- The `(ab)`-block tag `φ = hingeRow a b ρ'`: relabel to the genuine `e_b`-row.
    have hba : b ≠ a := Ne.symm hab
    have hbv : b ≠ v := Ne.symm hvb
    rw [BodyHingeFramework.hingeRow_funLeft_dualMap, Equiv.swap_apply_left,
      Equiv.swap_apply_of_ne_of_ne hba hbv]
    refine Or.inl ⟨e_b, v, b, ?_, ρ', ?_, rfl⟩
    · rw [hFva, PanelHingeFramework.toBodyHinge_graph, PanelHingeFramework.ofNormals_graph,
        Graph.removeVertex_isLink]
      exact ⟨hG_eb, hva, hba⟩
    · -- block: `Fva.supportExtensor e_b = panelSupportExtensor n_a n_b` (`ends₃ e_b = (v,b)`,
      -- `qρ(v,·) = q(a,·)`, `qρ(b,·) = q(b,·)`); the input gives `ρ' ⊥` it.
      rw [BodyHingeFramework.mem_hingeRowBlock_iff, hFva,
        PanelHingeFramework.toBodyHinge_supportExtensor, PanelHingeFramework.ofNormals_normal,
        PanelHingeFramework.ofNormals_normal, PanelHingeFramework.ofNormals_ends, hends₃_eb]
      simp only [hqρ, Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne hba hbv]
      exact hρ'e₀

/-- **G4d-i — the `a`-column restriction of a `G_v`-row-span vector lies in `hingeRowBlock e_c`**
(`lem:case-III-claim612-eq644`, §1.49(4), Phase 22h). Given `wGv` in the span of a framework
`Fv`'s rigidity rows and the degree-2-at-`a` constraint that `e_c` is the *only* edge of `Fv`
incident to `a` (endpoints `a`, `c` with `a ≠ c`), the column restriction `wGv ∘ single a` lies
in the `e_c`-hinge-row block of a second framework `Fab` whose `e_c`-block agrees with `Fv`'s
(`hblock`).

The proof is a `Submodule.span_induction` on `hwGv`:
- For each generator `hingeRow u w ρ ∈ Fv.rigidityRows` (link `f u w`, `ρ ∈ Fv.hingeRowBlock f`):
  - If `u = a`: then `hdeg2 f w hlink` forces `f = e_c`, so
    `ρ ∈ Fv.hingeRowBlock e_c = Fab.hingeRowBlock e_c`
    and `(hingeRow a w ρ) ∘ single a = ρ` (`hingeRow_comp_single_tail hac`).
  - If `w = a` (but `u ≠ a`): `hdeg2r f u hlink` forces `f = e_c`; rewrite via `hingeRow_swap`
    (`hingeRow u a ρ = hingeRow a u (−ρ)`) and `hingeRow_comp_single_tail`; the block is a
    submodule so `−ρ` stays in it.
  - Otherwise `u ≠ a` and `w ≠ a`: `hingeRow_comp_single_off` gives zero, which is in any block.
- The `zero`, `add`, and `smul` cases follow from submodule closure. -/
theorem BodyHingeFramework.acolumn_mem_hingeRowBlock_of_span_rigidityRows
    [DecidableEq α] {Fab Fv : BodyHingeFramework k α β}
    {a c : α} {e_c : β}
    (hac : a ≠ c)
    (hlink_ec : Fv.graph.IsLink e_c a c)
    (hblock : Fv.hingeRowBlock e_c = Fab.hingeRowBlock e_c)
    (hdeg2 : ∀ f x, Fv.graph.IsLink f a x → f = e_c)
    (hdeg2r : ∀ f x, Fv.graph.IsLink f x a → f = e_c)
    {wGv : Module.Dual ℝ (α → ScrewSpace k)}
    (hwGv : wGv ∈ Submodule.span ℝ Fv.rigidityRows) :
    wGv.comp (LinearMap.single ℝ (fun _ : α => ScrewSpace k) a) ∈ Fab.hingeRowBlock e_c := by
  -- Apply span_induction with the transported predicate `φ.comp(single a) ∈ Fab.hingeRowBlock e_c`.
  apply Submodule.span_induction (p := fun ψ _ =>
    ψ.comp (LinearMap.single ℝ (fun _ : α => ScrewSpace k) a) ∈ Fab.hingeRowBlock e_c) _ _ _ _ hwGv
  · -- generator case: hingeRow u w ρ ∈ Fv.rigidityRows
    rintro ψ ⟨f, u, w, hlink, ρ, hρ, rfl⟩
    by_cases hau : u = a
    · -- u = a: hdeg2 forces f = e_c; use links to get w = c
      have hfe : f = e_c := by rw [hau] at hlink; exact hdeg2 f w hlink
      -- hlink rewritten: IsLink e_c a w; use eq_and_eq_or_eq_and_eq with hlink_ec
      have hwc : w = c := by
        rw [hau, hfe] at hlink
        -- hlink : IsLink e_c a w; hlink_ec : IsLink e_c a c → a = a ∧ w = c ∨ a = c ∧ w = a
        rcases hlink.eq_and_eq_or_eq_and_eq hlink_ec with ⟨-, h⟩ | ⟨h, -⟩
        · exact h
        · exact absurd h hac
      rw [hau, hwc, hingeRow_comp_single_tail hac]
      exact hblock ▸ hfe ▸ hρ
    · by_cases haw : w = a
      · -- w = a, u ≠ a: hdeg2r forces f = e_c; use links to get u = c
        have hfe : f = e_c := by rw [haw] at hlink; exact hdeg2r f u hlink
        have huc : u = c := by
          rw [haw, hfe] at hlink
          -- hlink : IsLink e_c u a; hlink_ec : IsLink e_c a c → u = a ∧ a = c ∨ u = c ∧ a = a
          rcases hlink.eq_and_eq_or_eq_and_eq hlink_ec with ⟨h, -⟩ | ⟨h, -⟩
          · exact absurd h hau
          · exact h
        -- hingeRow u w ρ = hingeRow u a ρ; rewrite via hingeRow_swap, then
        -- hingeRow_comp_single_tail
        rw [hfe] at hρ
        rw [haw, hingeRow_swap u a ρ, huc, hingeRow_comp_single_tail hac]
        exact (Fab.hingeRowBlock e_c).neg_mem (hblock ▸ hρ)
      · -- u ≠ a, w ≠ a: off-column; restricts to 0
        rw [hingeRow_comp_single_off (Ne.symm hau) (Ne.symm haw)]
        exact (Fab.hingeRowBlock e_c).zero_mem
  · -- zero
    simp [(Fab.hingeRowBlock e_c).zero_mem]
  · -- add
    intro x y _ _ hx hy
    rw [LinearMap.add_comp]
    exact (Fab.hingeRowBlock e_c).add_mem hx hy
  · -- smul
    intro r x _ hx
    rw [LinearMap.smul_comp]
    exact (Fab.hingeRowBlock e_c).smul_mem r hx

/-- **G4d-ii — the `M₃` candidate hinge row lies in the `a`-split rigidity-row span**
(`lem:case-III-claim612-eq644`, §1.49(4), Phase 22h). From G4d-i
(`acolumn_mem_hingeRowBlock_of_span_rigidityRows`) —
`r̂ := wGv.comp(single a) ∈ Fab.hingeRowBlock e_c`
— together with `hingeRow_mem_rigidityRows` (the membership certificate for a single hinge row),
the row `hingeRow a c r̂` lies in the rigidity-row *set* of the `v`-split framework `Fv` (since
`hlink_ec : Fv.graph.IsLink e_c a c` and `hblock ▸ hr̂`), and hence in the
`Submodule.span` of `Fv.rigidityRows`.

This is the `M₃` analogue of `exists_candidate_row_eq612`'s `hcand_mem` output: the common
candidate vector `r̂` — the `a`-column restriction of the `G_v`-redundant row — serves as the
block functional for a `hingeRow a c r̂` rigidity row, whose `e_c`-hinge lies in `Fv`. -/
theorem BodyHingeFramework.hingeRow_acolumn_mem_span_rigidityRows
    [DecidableEq α] {Fab Fv : BodyHingeFramework k α β}
    {a c : α} {e_c : β}
    (hac : a ≠ c)
    (hlink_ec : Fv.graph.IsLink e_c a c)
    (hblock : Fv.hingeRowBlock e_c = Fab.hingeRowBlock e_c)
    (hdeg2 : ∀ f x, Fv.graph.IsLink f a x → f = e_c)
    (hdeg2r : ∀ f x, Fv.graph.IsLink f x a → f = e_c)
    {wGv : Module.Dual ℝ (α → ScrewSpace k)}
    (hwGv : wGv ∈ Submodule.span ℝ Fv.rigidityRows) :
    BodyHingeFramework.hingeRow (k := k) (α := α) a c
        (wGv.comp (LinearMap.single ℝ (fun _ : α => ScrewSpace k) a))
      ∈ Submodule.span ℝ Fv.rigidityRows := by
  apply Submodule.subset_span
  apply hingeRow_mem_rigidityRows Fv hlink_ec
  rw [hblock]
  exact acolumn_mem_hingeRowBlock_of_span_rigidityRows hac hlink_ec hblock hdeg2 hdeg2r hwGv

/-- **W9c — the `M₃` arm closer: the third candidate (the line `L'' ⊂ Π(c)`) realizes the `d = 3`
framework at full rank** (`lem:case-II-realization` / `lem:case-III`, the third of the three
`hcand`-discharge arms; Katoh–Tanigawa 2011 §6.4.1, eqs.~(6.31)–(6.44), the `M₃ = (r̂; r(L''))`
arm, design §1.52(d), Phase 22h). The `M₃` arm carries the candidate line `L'' ⊂ Π(c)` at the
*third* body `c` (the neighbour of `a` across the degree-2 edge `e_c = ac`), introduced by the
isomorphism `ρ : (G, p₃) ≅ (G_v^{ab}, q)` of KT eq.~(6.31) that relabels `a ↔ v`. The key
structural fact (KT eqs.~(6.35)–(6.41)) is that `R(G, p₃)`'s relevant submatrix *is* the v-split
matrix read through the relabel: the bottom block of (6.41) is the same `R(G_v^{ab} ∖ (ab)i^*, q)`
as the `M₁`/`M₂` arms, with the same `λ`s and the same redundant index `i^*`. So the `M₃` arm
consumes the **same** candidate/bottom data `ρ`/`w` as `M₁`/`M₂` (one W6b invocation feeds all
three; KT p. 686), transported *pointwise* across the vertex relabel `(a v)` by the W9a/W9b
leaves — there is no a-split rank certification, hence no second GAP-6.

This is a pure instantiation of `case_III_arm_realization` (W7) at the roles
`(v, a, b, e_a, e_b, n') := (a, c, v, e_c, e_a, n''')`, with the `Gv`-slot `G.removeVertex a` (the
relabeled split minus its short-circuit edge — a subgraph of `G`), the relabeled seed
`qρ = q ∘ (a v)` (inline `fun p => q (Equiv.swap a v p.1, p.2)`), the candidate functional
`ρ̃ := -ρ` (KT eq.~(6.44): `Σ λ_{(ac)j} r_j(q(ac)) = -r̂`; the negation is a Lean-orientation
artifact, `hingeRow c v (-ρ) = hingeRow v c ρ`), and the bottom family
`w̃ := (funLeft (a v)).dualMap ∘ w`. The heavy transports are delegated: the candidate
`hρe₀`-slot to **G4d-i** (`ρ ⊥ C(q(ac))`), the candidate `hρGv`-slot to **W9a** (the
short-circuit-free span transport into the `G − a`-row span), and the bottom `hwmem`-slot to
**W9b** (the per-member tag transport). Graph-free transport over the carrier; the §38 trap lives
inside W7. -/
theorem PanelHingeFramework.case_III_arm_realization_M3
    [Finite α] [Finite β] [DecidableEq α]
    (G : Graph α β) (ends₀ ends₃ : β → α × α) {q : α × Fin (k + 2) → ℝ}
    {v a b c : α} {e_a e_b e_c : β}
    (hva : v ≠ a) (hab : a ≠ b) (hvb : v ≠ b) (hca : c ≠ a) (hcv : c ≠ v)
    (hG_ea : G.IsLink e_a v a) (hG_eb : G.IsLink e_b v b) (hG_ec : G.IsLink e_c a c)
    (heac : e_a ≠ e_c)
    (hcla : ∀ e x, G.IsLink e a x → e = e_a ∨ e = e_c)
    (hrecGv : ∀ e x y, (G.removeVertex v).IsLink e x y →
      ends₀ e = (x, y) ∨ ends₀ e = (y, x))
    (hends₃_ec : ends₃ e_c = (a, c)) (hends₃_ea : ends₃ e_a = (a, v))
    (hends₃_eb : ends₃ e_b = (v, b))
    (hends₃_off : ∀ e, e ≠ e_a → e ≠ e_b → e ≠ e_c → ends₃ e = ends₀ e)
    (hends_Gva : ∀ e x y, (G.removeVertex a).IsLink e x y →
      (G.removeVertex a).IsLink e (ends₃ e).1 (ends₃ e).2)
    (hne_Gva : ∀ e, (G.removeVertex a).IsLink e (ends₃ e).1 (ends₃ e).2 →
      (PanelHingeFramework.ofNormals (G.removeVertex a) ends₃
        (fun p => q (Equiv.swap a v p.1, p.2))).toBodyHinge.supportExtensor e ≠ 0)
    (hV3 : 3 ≤ V(G).ncard)
    {n''' : Fin (k + 2) → ℝ}
    (hLn : LinearIndependent ℝ ![(fun i => q (c, i)), n'''])
    (hgca : LinearIndependent ℝ ![(fun i => q (c, i)), (fun i => q (a, i))])
    {ρ : Module.Dual ℝ (ScrewSpace k)}
    (hρgate : ρ (panelSupportExtensor (fun i => q (c, i)) n''') ≠ 0)
    (hρe₀ : ρ (panelSupportExtensor (fun i => q (a, i)) (fun i => q (b, i))) = 0)
    (hρGv : BodyHingeFramework.hingeRow a b ρ ∈ Submodule.span ℝ
      (PanelHingeFramework.ofNormals (G.removeVertex v) ends₀ q).toBodyHinge.rigidityRows)
    {ιb : Type*} [Finite ιb] {w : ιb → Module.Dual ℝ (α → ScrewSpace k)}
    (hwcard : Nat.card ιb = screwDim k * (V(G).ncard - 2))
    (hw : LinearIndependent ℝ w)
    (hwmem : ∀ j, w j ∈
        (PanelHingeFramework.ofNormals (G.removeVertex v) ends₀ q).toBodyHinge.rigidityRows ∨
      ∃ ρ' : Module.Dual ℝ (ScrewSpace k),
        ρ' (panelSupportExtensor (fun i => q (a, i)) (fun i => q (b, i))) = 0 ∧
        w j = BodyHingeFramework.hingeRow a b ρ')
    {n : ℕ} (hdef : G.deficiency n = 0) :
    PanelHingeFramework.HasGenericFullRankRealization k n G := by
  classical
  set qρ : α × Fin (k + 2) → ℝ := fun p => q (Equiv.swap a v p.1, p.2) with hqρ
  set Fv := (PanelHingeFramework.ofNormals (G.removeVertex v) ends₀ q).toBodyHinge with hFv
  -- The relabeled seed reads `q` at the swapped body: `qρ(c,·) = q(c,·)`, `qρ(v,·) = q(a,·)`.
  have hqρc : (fun i => qρ (c, i)) = (fun i => q (c, i)) := by
    funext i; rw [hqρ]; simp only [Equiv.swap_apply_of_ne_of_ne hca hcv]
  have hqρv : (fun i => qρ (v, i)) = (fun i => q (a, i)) := by
    funext i; rw [hqρ]; simp only [Equiv.swap_apply_right]
  -- The `e_c`-link of `Fv = ofNormals (G − v) ends₀ q`: `e_c` survives `removeVertex v`
  -- (endpoints `a, c ≠ v`).
  have hGv_ec : (G.removeVertex v).IsLink e_c a c :=
    Graph.removeVertex_isLink.mpr ⟨hG_ec, hva.symm, hcv⟩
  have hFv_link_ec : Fv.graph.IsLink e_c a c := by
    rw [hFv, PanelHingeFramework.toBodyHinge_graph, PanelHingeFramework.ofNormals_graph]
    exact hGv_ec
  -- Degree-2 at `a` inside `Fv`: the only `(G − v)`-link at `a` is `e_c` (the `e_a` branch links
  -- `v` and so cannot survive `removeVertex v`).
  have hdeg2 : ∀ f x, Fv.graph.IsLink f a x → f = e_c := by
    intro f x hlink
    rw [hFv, PanelHingeFramework.toBodyHinge_graph, PanelHingeFramework.ofNormals_graph] at hlink
    obtain ⟨hGlink, _, hxv⟩ := Graph.removeVertex_isLink.mp hlink
    rcases hcla f x hGlink with rfl | rfl
    · rcases hG_ea.eq_and_eq_or_eq_and_eq hGlink with ⟨h, _⟩ | ⟨h, _⟩
      · exact absurd h hva
      · exact absurd h.symm hxv
    · rfl
  have hdeg2r : ∀ f x, Fv.graph.IsLink f x a → f = e_c := fun f x hlink => hdeg2 f x hlink.symm
  -- The candidate functional's annihilation `ρ ⊥ C(q(ac))` via G4d-i (the `a`-column of
  -- `hingeRow a b ρ` is `ρ`, which lands in `Fv.hingeRowBlock e_c`, i.e. `ρ ⊥ Fv.supportExtensor
  -- e_c = ±C(q(ac))`).
  have hρ_ac : ρ (panelSupportExtensor (fun i => q (a, i)) (fun i => q (c, i))) = 0 := by
    have hcol :=
      BodyHingeFramework.acolumn_mem_hingeRowBlock_of_span_rigidityRows (Fab := Fv) (Fv := Fv)
        (a := a) (c := c) (e_c := e_c) (Ne.symm hca) hFv_link_ec rfl hdeg2 hdeg2r hρGv
    rw [BodyHingeFramework.hingeRow_comp_single_tail hab] at hcol
    have hperp := (Fv.mem_hingeRowBlock_iff e_c ρ).1 hcol
    rw [hFv, PanelHingeFramework.toBodyHinge_supportExtensor, PanelHingeFramework.ofNormals_normal,
      PanelHingeFramework.ofNormals_normal, PanelHingeFramework.ofNormals_ends] at hperp
    -- `ends₀ e_c ∈ {(a,c),(c,a)}`; either gives `ρ ⊥ ±C(q(ac))`.
    rcases hrecGv e_c a c hGv_ec with he | he
    · rwa [he] at hperp
    · rw [he, panelSupportExtensor_swap, map_neg, neg_eq_zero] at hperp; exact hperp
  -- The genuine `e_b`-row of the `M₃` framework `Fva = ofNormals (G − a) ends₃ qρ`.
  set Fva := (PanelHingeFramework.ofNormals (G.removeVertex a) ends₃ qρ).toBodyHinge with hFva
  -- `c, v ∈ V(G − a)` and `a ∉ V(G − a)`.
  have ha_mem : a ∈ V(G) := hG_ea.right_mem
  have hc_mem : c ∈ V(G) := hG_ec.right_mem
  have hv_mem : v ∈ V(G) := hG_ea.left_mem
  have hcard_Gva : V(G.removeVertex a).ncard = V(G).ncard - 1 := by
    rw [Graph.vertexSet_removeVertex, Set.ncard_diff_singleton_of_mem ha_mem]
  refine PanelHingeFramework.case_III_arm_realization (k := k) G (G.removeVertex a) ends₃
    (q := qρ) (v := a) (a := c) (b := v) (e_a := e_c) (e_b := e_a) (n' := n''')
    ?hvVc ?haVc ?hbVc hG_ec hG_ea.symm hends₃_ec hends₃_ea heac.symm
    ?hleG ?hsplitG hends_Gva hne_Gva ?hVone ?hVcard ?hLn ?hgab
    (ρ := -ρ) ?hρgate ?hρe₀ ?hρGv (ιb := ιb)
    (w := (LinearMap.funLeft ℝ (ScrewSpace k) (Equiv.swap a v)).dualMap ∘ w)
    ?hwcard ?hw ?hwmem hdef
  case hvVc => rw [Graph.vertexSet_removeVertex]; exact fun h => h.2 rfl
  case haVc => rw [Graph.vertexSet_removeVertex]; exact ⟨hc_mem, hca⟩
  case hbVc => rw [Graph.vertexSet_removeVertex]; exact ⟨hv_mem, hva⟩
  case hleG => exact fun e u w hlink => (Graph.removeVertex_isLink.mp hlink).1
  case hsplitG =>
    intro e u w hlink
    by_cases hua : u = a
    · subst u; rcases hcla e w hlink with rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl rfl
    · by_cases hwa : w = a
      · subst w; rcases hcla e u hlink.symm with rfl | rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inl rfl
      · exact Or.inr (Or.inr (Graph.removeVertex_isLink.mpr ⟨hlink, hua, hwa⟩))
  case hVone => rw [hcard_Gva]; omega
  case hVcard => rw [hcard_Gva]; omega
  case hLn => rw [hqρc]; exact hLn
  case hgab => rw [hqρc, hqρv]; exact hgca
  case hρgate =>
    rw [hqρc, LinearMap.neg_apply, neg_ne_zero]; exact hρgate
  case hρe₀ =>
    rw [hqρc, hqρv, LinearMap.neg_apply, panelSupportExtensor_swap, map_neg, hρ_ac,
      neg_zero, neg_zero]
  case hρGv =>
    -- `hingeRow c v (-ρ) = hingeRow v c ρ ∈ span Fva.rigidityRows`. From W9a at
    -- `φ := hingeRow a b ρ` (image `hingeRow v b ρ`, `a`-column `ρ`), giving
    -- `hingeRow v b ρ - hingeRow v c ρ ∈ span`;
    -- `hingeRow v b ρ` is the genuine `e_b`-row of `Fva` (via `hρe₀`), so `Submodule.sub_mem`.
    rw [BodyHingeFramework.hingeRow_swap c v (-ρ), neg_neg]
    have htrans : ∀ f x y, Fv.graph.IsLink f x y → x ≠ a → y ≠ a →
        Fva.graph.IsLink f x y ∧ Fv.hingeRowBlock f ≤ Fva.hingeRowBlock f := by
      intro f x y hlink hxa hya
      rw [hFv, PanelHingeFramework.toBodyHinge_graph, PanelHingeFramework.ofNormals_graph] at hlink
      obtain ⟨hGflink, hxv, hyv⟩ := Graph.removeVertex_isLink.mp hlink
      have hfne_a : f ≠ e_a := by
        rintro rfl
        rcases hG_ea.eq_and_eq_or_eq_and_eq hGflink with ⟨hh, _⟩ | ⟨hh, _⟩
        · exact hxv hh.symm
        · exact hyv hh.symm
      have hfne_b : f ≠ e_b := by
        rintro rfl
        rcases hG_eb.eq_and_eq_or_eq_and_eq hGflink with ⟨hh, _⟩ | ⟨hh, _⟩
        · exact hxv hh.symm
        · exact hyv hh.symm
      have hfne_c : f ≠ e_c := by
        rintro rfl
        rcases hG_ec.eq_and_eq_or_eq_and_eq hGflink with ⟨hh, _⟩ | ⟨hh, _⟩
        · exact hxa hh.symm
        · exact hya hh.symm
      refine ⟨?_, ?_⟩
      · rw [hFva, PanelHingeFramework.toBodyHinge_graph, PanelHingeFramework.ofNormals_graph,
          Graph.removeVertex_isLink]
        exact ⟨hGflink, hxa, hya⟩
      · -- the `f`-extensors at `Fva` and `Fv` coincide off `{e_a, e_b, e_c}` (`ends₃ f = ends₀ f`,
        -- `qρ = q` at the recorded endpoints `∉ {a, v}`), so the blocks are equal.
        intro r hr
        rw [Fva.mem_hingeRowBlock_iff]
        rw [Fv.mem_hingeRowBlock_iff] at hr
        rw [hFva, PanelHingeFramework.toBodyHinge_supportExtensor,
          PanelHingeFramework.ofNormals_normal, PanelHingeFramework.ofNormals_normal,
          PanelHingeFramework.ofNormals_ends, hends₃_off f hfne_a hfne_b hfne_c]
        rw [hFv, PanelHingeFramework.toBodyHinge_supportExtensor,
          PanelHingeFramework.ofNormals_normal, PanelHingeFramework.ofNormals_normal,
          PanelHingeFramework.ofNormals_ends] at hr
        rcases hrecGv f x y hlink with he | he <;> rw [he] at hr ⊢ <;>
          simp only [hqρ, Equiv.swap_apply_of_ne_of_ne hxa hxv,
            Equiv.swap_apply_of_ne_of_ne hya hyv] <;> exact hr
    have hw9a := BodyHingeFramework.funLeft_dualMap_sub_acolumn_mem_span_rigidityRows
      (Fv := Fv) (Fva := Fva) (v := v) (a := a) (c := c) (e_c := e_c)
      hca hcv hFv_link_ec hdeg2 hdeg2r
      (fun f x y hlink => by
        rw [hFv, PanelHingeFramework.toBodyHinge_graph,
          PanelHingeFramework.ofNormals_graph] at hlink
        exact (Graph.removeVertex_isLink.mp hlink).2)
      htrans (φ := BodyHingeFramework.hingeRow a b ρ) hρGv
    -- `(funLeft (a v)).dualMap (hingeRow a b ρ) = hingeRow v b ρ`; `a`-column is `ρ`.
    rw [BodyHingeFramework.hingeRow_funLeft_dualMap, Equiv.swap_apply_left,
      Equiv.swap_apply_of_ne_of_ne (Ne.symm hab) (Ne.symm hvb),
      BodyHingeFramework.hingeRow_comp_single_tail hab] at hw9a
    -- `hingeRow v b ρ` is the genuine `e_b`-row of `Fva`.
    have hvb_row : BodyHingeFramework.hingeRow v b ρ ∈ Submodule.span ℝ Fva.rigidityRows := by
      refine Submodule.subset_span ⟨e_b, v, b, ?_, ρ, ?_, rfl⟩
      · rw [hFva, PanelHingeFramework.toBodyHinge_graph, PanelHingeFramework.ofNormals_graph,
          Graph.removeVertex_isLink]
        exact ⟨hG_eb, hva, Ne.symm hab⟩
      · rw [Fva.mem_hingeRowBlock_iff, hFva, PanelHingeFramework.toBodyHinge_supportExtensor,
          PanelHingeFramework.ofNormals_normal, PanelHingeFramework.ofNormals_normal,
          PanelHingeFramework.ofNormals_ends, hends₃_eb]
        simp only [hqρ, Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne (Ne.symm hab)
          (Ne.symm hvb)]
        exact hρe₀
    have := Submodule.sub_mem _ hvb_row hw9a
    rwa [sub_sub_cancel] at this
  case hwcard =>
    -- both `w̃` and `w` index by `ιb`; the count matches (`V(G − a).ncard − 1 = V(G).ncard − 2`).
    rw [hwcard, hcard_Gva, Nat.sub_sub]
  case hw =>
    exact hw.map' _ (LinearMap.ker_eq_bot.2
      (LinearMap.dualMap_injective_of_surjective
        (LinearMap.funLeft_surjective_of_injective _ _ (Equiv.swap a v) (Equiv.injective _))))
  case hwmem =>
    intro j
    -- bridge the `∘` and the `qρ(c,·)/qρ(v,·) = q(c,·)/q(a,·)` seed identities, then W9b.
    simp only [Function.comp_apply, hqρc, hqρv]
    exact PanelHingeFramework.case_III_bottom_relabel hva hab hvb hca hcv hG_ea hG_eb hG_ec hcla
      (fun e x y hlink => (Graph.removeVertex_isLink.mp hlink).1)
      (fun e x y hlink => ⟨(Graph.removeVertex_isLink.mp hlink).2.1,
        (Graph.removeVertex_isLink.mp hlink).2.2⟩)
      (fun e x y hlink => hrecGv e x y hlink) hends₃_eb hends₃_off (hwmem j)

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

/-- **Triple linear independence from algebraic independence** (§1.48(2), the triple-LI bridge;
Phase 22h). For three distinct vertices `a, b, c` in an algebraically-independent-over-`ℚ` family
`q : α × Fin 4 → ℝ`, the three row vectors `![q(a,·), q(b,·), q(c,·)]` are `ℝ`-linearly independent.

This is the bridge the Case-III `hcand` discharge needs: the IH carries
`AlgebraicIndependent ℚ (fun p => Q.normal p.1 p.2)`, and the `d = 3` placement uses three
distinct normals `n_a = q(a,·)`, `n_b = q(b,·)`, `n_c = q(c,·)` as input to
`exists_homogeneousIncidence_of_normals`. General position (`IsGeneralPosition Q`, pairwise LI,
§1.41(2)) gives the pairwise `hgab`; this lemma provides the triple LI.

**Proof route** (det-polynomial, §1.48(2)): form the `3×3` submatrix `B i j = q([a,b,c][i],
Fin.castSucc j)` (first three coordinates of each row). Show `B.det ≠ 0` by:
(i) `B = (mvPolynomialX Fin3 Fin3 ℚ).map (eval₂ (algebraMap ℚ ℝ) (q ∘ f))`
    where `f (i,j) = ([a,b,c][i], Fin.castSucc j)` (by `mvPolynomialX_map_eval₂`);
(ii) `B.det = eval₂ (algebraMap ℚ ℝ) (q ∘ f) (det (mvPolynomialX ...))`
    (by `RingHom.map_det`);
(iii) `det (mvPolynomialX Fin3 Fin3 ℚ) ≠ 0` (`Matrix.det_mvPolynomialX_ne_zero`);
(iv) `q ∘ f` is alg-indep over ℚ (`AlgebraicIndependent.comp`, since `f` is injective by `a,b,c`
     distinct and `Fin.castSucc` injective);
(v) `eval_ne_zero_of_coeffs_subset_range_of_algebraicIndependent` certifies `B.det ≠ 0`.
Then `Matrix.linearIndependent_rows_of_det_ne_zero` + `LinearIndependent.of_comp` (projection to
first 3 coordinates) lifts to the full 4-coordinate rows. -/
private lemma linearIndependent_normals_of_algebraicIndependent
    {α : Type*} {q : α × Fin 4 → ℝ}
    (hq : AlgebraicIndependent ℚ q)
    {a b c : α} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    LinearIndependent ℝ (![fun i => q (a, i), fun i => q (b, i), fun i => q (c, i)] :
      Fin 3 → Fin 4 → ℝ) := by
  classical
  -- Suffices: the projection to the first 3 coordinates is also independent.
  -- If the full-row family is dependent, so is the projected family; so we prove LI of the
  -- projected family (rows of the 3×3 matrix B) and lift back.
  apply LinearIndependent.of_comp
    (LinearMap.pi (fun j : Fin 3 => (LinearMap.proj (Fin.castSucc j) : (Fin 4 → ℝ) →ₗ[ℝ] ℝ)))
  -- The composed family equals the rows of the 3×3 matrix B i j = q([a,b,c][i], Fin.castSucc j).
  have hcomp_eq : (LinearMap.pi
        (fun j : Fin 3 => (LinearMap.proj (Fin.castSucc j) : (Fin 4 → ℝ) →ₗ[ℝ] ℝ))) ∘
      (![fun i => q (a, i), fun i => q (b, i), fun i => q (c, i)] : Fin 3 → Fin 4 → ℝ) =
      fun (i : Fin 3) (j : Fin 3) => q (![a, b, c] i, Fin.castSucc j) := by
    ext i j; fin_cases i <;> rfl
  rw [hcomp_eq]
  -- Show the 3×3 matrix B has nonzero determinant (rows are then linearly independent).
  apply Matrix.linearIndependent_rows_of_det_ne_zero
  -- Set up the injection f : Fin 3 × Fin 3 → α × Fin 4.
  set f : Fin 3 × Fin 3 → α × Fin 4 := fun p => (![a, b, c] p.1, Fin.castSucc p.2) with hf_def
  have hfinj : Function.Injective f := by
    intro ⟨i, j⟩ ⟨i', j'⟩ heq
    simp only [hf_def, Prod.mk.injEq] at heq
    have hjeq : j = j' := Fin.castSucc_injective _ heq.2
    subst hjeq
    suffices hi : i = i' by exact Prod.ext hi rfl
    fin_cases i <;> fin_cases i' <;>
      simp_all [Matrix.cons_val_zero, Matrix.cons_val_one]
  -- q∘f is algebraically independent over ℚ (injective precomposition of an alg-indep family).
  have hqf : AlgebraicIndependent ℚ (q ∘ f) := hq.comp f hfinj
  -- The generic 3×3 det polynomial P = det(mvPolynomialX) is nonzero over ℚ.
  have hP_ne : (Matrix.mvPolynomialX (Fin 3) (Fin 3) ℚ).det ≠ 0 :=
    Matrix.det_mvPolynomialX_ne_zero (Fin 3) ℚ
  -- B.det = aeval(q∘f) P.  Use mvPolynomialX_mapMatrix_aeval: aeval(A.·) (mvPolynomialX) = A,
  -- then take .det and apply RingHom.map_det.
  suffices hBdet :
      Matrix.det (fun i j => q (![a, b, c] i, Fin.castSucc j)) =
      MvPolynomial.aeval (fun p : Fin 3 × Fin 3 => (q ∘ f) p)
        (Matrix.mvPolynomialX (Fin 3) (Fin 3) ℚ).det by
    rw [hBdet]
    exact hqf.aeval_ne_zero hP_ne
  -- Prove B.det = aeval(q∘f) det(mvPolynomialX).
  -- B = (aeval (q∘f)).mapMatrix (mvPolynomialX) by mvPolynomialX_mapMatrix_aeval;
  -- B.det = (aeval (q∘f)) (mvPolynomialX.det) by AlgHom.map_det.
  -- B.det = aeval(q∘f) (det mvPolynomialX).
  -- Step 1: (aeval (fun p => (q∘f) p)).mapMatrix (mvPolynomialX) = B
  --         (by mvPolynomialX_mapMatrix_aeval, since (q∘f) p = B p.1 p.2 definitionally).
  have hφB : (MvPolynomial.aeval (fun p : Fin 3 × Fin 3 => (q ∘ f) p)).mapMatrix
      (Matrix.mvPolynomialX (Fin 3) (Fin 3) ℚ) =
      (fun i j => q (![a, b, c] i, Fin.castSucc j)) := by
    have := Matrix.mvPolynomialX_mapMatrix_aeval ℚ
      (Matrix.of (fun i j : Fin 3 => q (![a, b, c] i, Fin.castSucc j)))
    simp only [Matrix.of_apply] at this
    convert this using 2
  -- Step 2: aeval(q∘f) (det mvPolynomialX) = (aeval(q∘f).mapMatrix (mvPolynomialX)).det
  --         by AlgHom.map_det (reversed direction).
  rw [← hφB, AlgHom.map_det]

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
  obtain ⟨ρ, w, hρne, hρe₀', hρGv', hw, hwmem'⟩ :=
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

/-- **The Case-III `d = 3` realization** (`lem:case-II-realization` / `lem:case-III`, the
`hsplitGP`-shaped producer wrapping the `d = 3` Case-III assembly at `k = 2`; Katoh–Tanigawa
2011 §6.4.1, Lemma 6.10, Phase 22h L5b′). Named wrapper for the inline wiring of
`case_III_hsplit_producer` + `case_III_candidate_dispatch` that `theorem_55_d3` threads
through `theorem_55_generic`'s `hsplitGP` slot.

Carries the two adjudicated hypotheses `hfresh` (fresh edge supply for the chain arm's
short-circuit edge) and `h622` (GAP 6, the eq.-(6.22) nested-IH rank lower bound — the
all-`k` successor sub-phase 22i discharges it). -/
theorem PanelHingeFramework.case_III_realization [DecidableEq β] [Finite α] [Finite β]
    {n : ℕ} (hD : 6 ≤ Graph.bodyBarDim n)
    (hfresh : ∀ G' : Graph α β, ∃ e₀ : β, e₀ ∉ E(G'))
    -- GAP 6 (adjudicated carry): see `theorem_55_d3`.
    (h622 : ∀ (G : Graph α β) (v a b : α) (e₀ : β)
        (ends : β → α × α) (q : α × Fin 4 → ℝ),
      (∀ e u w, (G.splitOff v a b e₀).IsLink e u w → ends e = (u, w) ∨ ends e = (w, u)) →
      (∀ x y : α, x ≠ y → LinearIndependent ℝ ![fun i => q (x, i), fun i => q (y, i)]) →
      AlgebraicIndependent ℚ q →
      screwDim 2 * (V(G.splitOff v a b e₀).ncard - 1) - (screwDim 2 - 2)
        ≤ Module.finrank ℝ (Submodule.span ℝ
            (PanelHingeFramework.ofNormals (G.removeVertex v) ends
              q).toBodyHinge.rigidityRows))
    (G : Graph α β) (hG : G.IsMinimalKDof n 0) (hV3 : 3 ≤ V(G).ncard)
    (hnoRigid : ∀ H : Graph α β, ¬ H.IsProperRigidSubgraph G n)
    (hSimple : G.Simple)
    (hIH : ∀ G' : Graph α β, G'.IsMinimalKDof n 0 → 2 ≤ V(G').ncard →
      V(G').ncard < V(G).ncard →
      (G'.Simple → PanelHingeFramework.HasGenericFullRankRealization 2 n G') ∧
        HasPanelRealization 2 n G') :
    PanelHingeFramework.HasGenericFullRankRealization 2 n G :=
  PanelHingeFramework.case_III_hsplit_producer hD G hG hV3 hnoRigid hSimple hIH hfresh
    (fun v a b c eₐ e_b e_c e₀ hvG haG hbG hcG hav hbv hba hcv hca hbc heab heac
        hlea hleb hlec hclv hcla he₀ hdef_Gab hsplitGP' =>
      PanelHingeFramework.case_III_candidate_dispatch G v a b c eₐ e_b e_c e₀
        hSimple hvG haG hbG hcG hav hbv hba hcv hca hbc heab heac
        hlea hleb hlec hclv hcla he₀
        (h622 G v a b e₀)
        hdef_Gab hG.1 hsplitGP')

/-- **Theorem 5.5 base producer, parallel-pair arm** (`lem:theorem-55-base-producer-parallel`, the
`|V| = 2`, `k = 0` arm; Katoh–Tanigawa 2011 §5/§6, Lemma 5.3, p. 670; Phase 22i L3b). The
genuinely-new geometric arm of the all-`k` base producer: a two-vertex minimal-`0`-dof-graph — a
*parallel pair* of edges `e ≠ f` both linking `x ≠ y`, with `V(G) = {x, y}` and `def(G̃) = 0`
(KT p. 671 case (iii), `isMinimalKDof_ncard_le_two_trichotomy`) — carries a genuine-hinge panel
realization at the full target rank `D(|V|−1) − def = D·1 = 6`.

The construction places *coincident panels* `Π(x) = Π(y) = n^⊥` at a fixed nonzero normal
`n := Pi.single 0 1` and assigns the two parallel hinges two **linearly-independent** supporting
extensors inside that common panel `n^⊥` (`exists_linearIndependent_extensor_pair_perp`, the L3a
brick). The two independent extensors give the combined hinge-row blocks full rank `D = 6` on the
relative screw `S x − S y`, so `theorem_55_base` makes the framework infinitesimally rigid on
`{x, y} = V(G)`; bridge **B1**
(`isInfinitesimallyRigidOn_vertexSet_iff_finrank_span_rigidityRows`) turns that into the M2 rank
equality. This is the `|V| = 2`, `k = 0` leaf KT's p. 670 Lemma 5.3 realizes; it bottoms out on the
two-independent-extensors-in-a-common-hyperplane device, the only new geometry the base producer
needs (the empty and single-edge arms are bookkeeping / single-row counts). -/
theorem theorem_55_base_producer_parallel_pair [Finite α] {n : ℕ}
    (G : Graph α β) {x y : α} {e f : β}
    (hxy : x ≠ y) (hef : e ≠ f) (hVG : V(G) = {x, y}) (hEG : E(G) = {e, f})
    (hl_e : G.IsLink e x y) (hl_f : G.IsLink f x y) (hdef : G.deficiency n = 0) :
    HasPanelRealization 2 n G := by
  classical
  -- A fixed nonzero panel normal `n₀ : Fin 4 → ℝ`; both bodies share the panel `n₀^⊥`.
  set n₀ : Fin 4 → ℝ := Pi.single 0 1 with hn₀
  have hn₀_ne : n₀ ≠ 0 := by
    intro h; have := congr_fun h 0; simp [hn₀, Pi.single_eq_same] at this
  -- The L3a geometric brick: two point-pairs in `n₀^⊥` with linearly-independent extensors.
  obtain ⟨p, q, hp_perp, hq_perp, hpq_li⟩ := exists_linearIndependent_extensor_pair_perp n₀
  set Ce : ScrewSpace 2 := ⟨extensor p, extensor_mem_exteriorPower _⟩ with hCe
  set Cf : ScrewSpace 2 := ⟨extensor q, extensor_mem_exteriorPower _⟩ with hCf
  -- The two-hinge framework: `e ↦ Ce`, `f ↦ Cf`, all other edges `0`.
  set F : BodyHingeFramework 2 α β :=
    { graph := G
      supportExtensor := fun e' => if e' = e then Ce else if e' = f then Cf else 0 } with hF
  -- The two supporting extensors reduce to `Ce`, `Cf`.
  have hFe : F.supportExtensor e = Ce := by simp [hF]
  have hFf : F.supportExtensor f = Cf := by simp [hF, hef.symm]
  -- `Ce`, `Cf` are nonzero (from their linear independence).
  have hCe_ne : Ce ≠ 0 := by simpa [hCe] using hpq_li.ne_zero 0
  have hCf_ne : Cf ≠ 0 := by simpa [hCf] using hpq_li.ne_zero 1
  -- Every link of `G` is at `e` or `f` (the parallel pair, `E(G) = {e, f}`).
  have hlink_cases : ∀ e' u v, G.IsLink e' u v → e' = e ∨ e' = f := by
    intro e' u v he'
    have : e' ∈ E(G) := he'.edge_mem
    rw [hEG] at this
    simpa [Set.mem_insert_iff] using this
  -- The vertex set has exactly two bodies.
  have hVcard : V(G).ncard = 2 := by rw [hVG, Set.ncard_pair hxy]
  -- `V(F.graph) = {x, y}` is nonempty.
  have hFg : F.graph = G := rfl
  have hne : F.graph.vertexSet.Nonempty := by rw [hFg, hVG]; exact ⟨x, Or.inl rfl⟩
  refine ⟨F, fun _ => n₀, rfl, ?_, ?_, ?_⟩
  · -- Every body has a nonzero panel normal (the fixed `n₀`).
    exact fun v _ => hn₀_ne
  · -- Every link's supporting extensor is nonzero and lies in both endpoint panels `n₀^⊥`.
    intro e' u v he'
    have hCein : ExtensorInPanel Ce n₀ := ⟨p, rfl, hp_perp⟩
    have hCfin : ExtensorInPanel Cf n₀ := ⟨q, rfl, hq_perp⟩
    rcases hlink_cases e' u v he' with rfl | rfl
    · rw [hFe]; exact ⟨hCe_ne, hCein, hCein⟩
    · rw [hFf]; exact ⟨hCf_ne, hCfin, hCfin⟩
  · -- The rank conjunct, via `theorem_55_base` (full rank on `{x,y}`) and bridge B1.
    -- The two LI supporting extensors at the two parallel hinges make `F` rigid on `{x, y}`.
    have hgen : LinearIndependent ℝ ![F.supportExtensor e, F.supportExtensor f] := by
      rw [hFe, hFf]; exact hpq_li
    have hrig : F.IsInfinitesimallyRigidOn {x, y} :=
      F.theorem_55_base hxy hgen hl_e hl_f
    have hrigV : F.IsInfinitesimallyRigidOn F.graph.vertexSet := by
      rw [hFg, hVG]; exact hrig
    -- B1 turns rigidity on `V(G)` into the full-rank count.
    have hB1 := (F.isInfinitesimallyRigidOn_vertexSet_iff_finrank_span_rigidityRows hne).mp hrigV
    rw [hFg] at hB1
    rw [hB1, hVcard, hdef]
    push_cast
    ring

/-- **Theorem 5.5 base producer, empty arm** (`lem:theorem-55-base-producer`; `hbase` carry,
Phase 22i L3b). The bookkeeping arm of the all-`k` base producer: a minimal-`k`-dof graph on
`1 ≤ |V| ≤ 2` with **empty edge set** (`E(G) = ∅`, trichotomy arm (i),
`isMinimalKDof_ncard_le_two_trichotomy`) carries a genuine-hinge panel realization at rank
`D(|V|−1) − def = D(|V|−1) − D(|V|−1) = 0`.

The all-zero-extensor framework `F := ⟨G, fun _ => 0⟩` fires no hinge constraint (no links), so
`rigidityRows F = ∅`, `span ∅ = ⊥`, and `finrank ⊥ = 0`. The per-link conjunct is vacuous
(`E(G) = ∅`). A fixed nonzero normal `n₀ := Pi.single 0 1` supplies the panel-normal conjunct. -/
theorem theorem_55_base_producer_empty [DecidableEq β] [Finite α] {n : ℕ}
    (hn : Graph.bodyBarDim n = screwDim 2)
    (G : Graph α β) (hE : E(G) = ∅)
    (hG : G.IsMinimalKDof n ((Graph.bodyBarDim n : ℤ) * ((V(G).ncard : ℤ) - 1))) :
    HasPanelRealization 2 n G := by
  classical
  -- A fixed nonzero panel normal `n₀ : Fin 4 → ℝ`.
  set n₀ : Fin 4 → ℝ := Pi.single 0 1 with hn₀
  have hn₀_ne : n₀ ≠ 0 := by
    intro h; have := congr_fun h 0; simp [hn₀, Pi.single_eq_same] at this
  -- The all-zero framework: all supporting extensors are zero.
  set F : BodyHingeFramework 2 α β :=
    { graph := G
      supportExtensor := fun _ => 0 } with hF
  have hFg : F.graph = G := rfl
  -- No edge links in `G` (since `E(G) = ∅`), so `rigidityRows F = ∅`.
  have hnoLink : ∀ e u v, ¬ G.IsLink e u v := by
    intro e u v hlink
    have : e ∈ E(G) := hlink.edge_mem
    simp [hE] at this
  have hrows : F.rigidityRows = ∅ := by
    ext φ; simp only [Set.mem_empty_iff_false, iff_false]
    rintro ⟨e, u, v, hlink, _⟩
    exact hnoLink e u v (hFg ▸ hlink)
  -- `span ∅ = ⊥` and `finrank ⊥ = 0`.
  have hfinrank : Module.finrank ℝ (Submodule.span ℝ F.rigidityRows) = 0 := by
    rw [hrows, Submodule.span_empty, finrank_bot]
  refine ⟨F, fun _ => n₀, rfl, ?_, ?_, ?_⟩
  · -- Every body has a nonzero panel normal.
    exact fun v _ => hn₀_ne
  · -- Per-link conjunct: vacuous since `E(G) = ∅`.
    intro e u v hlink
    exact absurd hlink (hnoLink e u v)
  · -- Rank conjunct: target = 0.
    -- `G.deficiency n = bodyBarDim n * (ncard - 1)` from `hG.1`.
    have hdef : (G.deficiency n : ℤ) = (Graph.bodyBarDim n : ℤ) * ((V(G).ncard : ℤ) - 1) :=
      hG.1
    rw [hfinrank]
    -- `screwDim 2 * (ncard - 1) - def = screwDim 2 * (ncard - 1) - screwDim 2 * (ncard - 1) = 0`
    rw [hdef, hn]
    push_cast
    ring

/-- **Theorem 5.5 base producer, single-edge arm** (`lem:theorem-55-base-producer`; `hbase` carry,
Phase 22i L3b). The second bookkeeping arm of the all-`k` base producer: a minimal-`1`-dof graph
`G` with `V(G) = {x, y}` and `E(G) = {e}` (a single hinge joining distinct bodies; trichotomy arm
(ii), `isMinimalKDof_ncard_le_two_trichotomy`) carries a genuine-hinge panel realization at rank
`D(|V|−1) − def = D·1 − 1 = D − 1 = 5` (at `d = 3`, `D = 6`).

The construction places one nonzero supporting extensor `C ∈ n₀^⊥` on the single edge (from the
L3a brick `exists_linearIndependent_extensor_pair_perp`, first component), and the zero extensor on
all other edges. The single hinge-row block has dimension `D − 1`
(`finrank_span_panelRow_edge`), and via `span_panelRow_linking_eq_rigidityRows` this equals the
full rigidity-row span. No upper-bound argument (B2) is needed: the equality follows directly from
the single-edge span identity. -/
theorem theorem_55_base_producer_single_edge [DecidableEq β] [Finite α] {n : ℕ}
    (G : Graph α β) {x y : α} {e : β}
    (hxy : x ≠ y) (hVG : V(G) = {x, y}) (hEG : E(G) = {e})
    (hl : G.IsLink e x y) (hG : G.IsMinimalKDof n 1) :
    HasPanelRealization 2 n G := by
  classical
  -- A fixed nonzero panel normal `n₀ : Fin 4 → ℝ`.
  set n₀ : Fin 4 → ℝ := Pi.single 0 1 with hn₀
  have hn₀_ne : n₀ ≠ 0 := by
    intro h; have := congr_fun h 0; simp [hn₀, Pi.single_eq_same] at this
  -- The L3a brick: two point-pairs in `n₀^⊥` with LI extensors; take the first pair.
  obtain ⟨p, _, hp_perp, _, hpq_li⟩ := exists_linearIndependent_extensor_pair_perp n₀
  set C : ScrewSpace 2 := ⟨extensor p, extensor_mem_exteriorPower _⟩ with hC_def
  have hC_ne : C ≠ 0 := by simpa [hC_def] using hpq_li.ne_zero 0
  -- `C` lies in `n₀^⊥` (as an extensor of two points in `n₀^⊥`).
  have hCin : ExtensorInPanel C n₀ := ⟨p, rfl, hp_perp⟩
  -- The single-edge framework: `e ↦ C`, all other edges `↦ 0`.
  set F : BodyHingeFramework 2 α β :=
    { graph := G
      supportExtensor := fun e' => if e' = e then C else 0 } with hF
  have hFg : F.graph = G := rfl
  have hFe : F.supportExtensor e = C := by simp [hF]
  -- Every link uses edge `e` (the only edge, `E(G) = {e}`).
  have hlink_e : ∀ e' u v, G.IsLink e' u v → e' = e := by
    intro e' u v he'
    have := he'.edge_mem; rw [hEG] at this
    exact Set.mem_singleton_iff.mp this
  -- The vertex set has ncard 2.
  have hVcard : V(G).ncard = 2 := by rw [hVG, Set.ncard_pair hxy]
  -- `V(F.graph)` is nonempty.
  have hFne : F.graph.vertexSet.Nonempty := by rw [hFg, hVG]; exact ⟨x, Or.inl rfl⟩
  refine ⟨F, fun _ => n₀, rfl, ?_, ?_, ?_⟩
  · -- Every body has a nonzero panel normal.
    exact fun v _ => hn₀_ne
  · -- Per-link conjunct: all links are at `e`, with extensor `C`.
    intro e' u v he'
    have he'e : e' = e := hlink_e e' u v he'
    subst he'e
    refine ⟨?_, ?_, ?_⟩
    · simp [hFe, hC_ne]
    · simp only [hFe]; exact hCin
    · simp only [hFe]; exact hCin
  · -- Rank conjunct: `finrank (span rigidityRows) = screwDim 2 - 1 = D * 1 - 1`.
    -- Use `span_panelRow_linking_eq_rigidityRows` with `ends := fun _ => (x, y)`.
    set ends : β → α × α := fun _ => (x, y) with hends_def
    have hends : ∀ e' u v, F.graph.IsLink e' u v →
        F.graph.IsLink e' (ends e').1 (ends e').2 := by
      intro e' u v he'
      simp only [hends_def]
      exact (hlink_e e' u v (hFg ▸ he')).symm ▸ (hFg ▸ hl)
    have hne_link : ∀ e', F.graph.IsLink e' (ends e').1 (ends e').2 →
        F.supportExtensor e' ≠ 0 := by
      intro e' he'
      have he'e : e' = e := hlink_e e' x y (hFg ▸ (by simpa [hends_def] using he'))
      subst he'e
      simpa [hFe]
    -- `span (linking panelRows) = span rigidityRows`.
    rw [← F.span_panelRow_linking_eq_rigidityRows hends hne_link]
    -- The linking subtype is exactly the `e`-rows (the only link is `e`).
    -- The range of linking panel rows equals the range for the single edge `e`.
    have hrange : Set.range (fun i : {i : β × Set.powersetCard (Fin 4) 2
          × Set.powersetCard (Fin 4) 2 //
            F.graph.IsLink i.1 (ends i.1).1 (ends i.1).2} => F.panelRow ends i.val)
        = Set.range (fun p : Set.powersetCard (Fin 4) 2
            × Set.powersetCard (Fin 4) 2 => F.panelRow ends (e, p.1, p.2)) := by
      ext φ; simp only [Set.mem_range]
      constructor
      · rintro ⟨⟨⟨e', t₁, t₂⟩, hlink⟩, rfl⟩
        have he'e : e' = e := hlink_e e' x y (hFg ▸ by simpa [hends_def] using hlink)
        exact ⟨(t₁, t₂), by simp [he'e]⟩
      · rintro ⟨⟨t₁, t₂⟩, rfl⟩
        exact ⟨⟨(e, t₁, t₂), by simpa [hends_def, hFg] using hl⟩, rfl⟩
    -- Now reduce to `finrank_span_panelRow_edge`.
    conv_lhs => rw [hrange]
    rw [F.finrank_span_panelRow_edge (huv := by simp [hends_def, hxy])
        (hne := by simp [hFe, hC_ne])]
    -- Target: `screwDim 2 * (ncard - 1 : ℤ) - deficiency n = screwDim 2 - 1`.
    have hdef : (G.deficiency n : ℤ) = 1 := hG.1
    rw [Nat.cast_sub (by decide : 1 ≤ screwDim 2)]
    push_cast [hVcard, hdef]
    ring

/-- **Theorem 5.5 base producer, empty arm — general-position form** (`lem:theorem-55-base`;
`hbase` carry's GP conjunct, Phase 22i L3b). The GP-conjunct companion of
`theorem_55_base_producer_empty`: a *simple* minimal-`k`-dof graph `G` with **empty edge set**
(`E(G) = ∅`, trichotomy arm (i)) carries a *generic* full-rank panel realization
(`HasGenericFullRankRealization`) at rank `D(|V|−1) − def = 0`.

The framework `ofNormals G ends q₀` is built at an injective algebraically-independent seed `q₀`
(`exists_injective_algebraicIndependent_real`), which is a non-root of the general-position
polynomial (`exists_generalPosition_polynomial`), so the panel normals are in general position and
algebraically independent. The rigidity-row span is `⊥` (no links fire, `E(G) = ∅`), so the rank is
`0 = screwDim 2 * (|V|−1) − def` (the empty arm's `def = screwDim 2 * (|V|−1)`). Link-recording is
vacuous (`E(G) = ∅`). -/
theorem theorem_55_base_producer_empty_gp [DecidableEq β] [Finite α] [Finite β] {n : ℕ}
    (hn : Graph.bodyBarDim n = screwDim 2)
    (G : Graph α β) (hE : E(G) = ∅) (hne : V(G).Nonempty)
    (hG : G.IsMinimalKDof n ((Graph.bodyBarDim n : ℤ) * ((V(G).ncard : ℤ) - 1))) :
    PanelHingeFramework.HasGenericFullRankRealization 2 n G := by
  classical
  -- No edge links in `G` (since `E(G) = ∅`).
  have hnoLink : ∀ e u v, ¬ G.IsLink e u v := by
    intro e u v hlink
    have : e ∈ E(G) := hlink.edge_mem
    simp [hE] at this
  -- The endpoint selector is irrelevant (no links); pick a constant body `w ∈ V(G)`.
  obtain ⟨w, _⟩ := hne
  set ends : β → α × α := fun _ => (w, w) with hends_def
  -- The general-position polynomial and an algebraically-independent injective seed `q₀`.
  obtain ⟨Qgp, hQgp_ne, hQgprat, hQgp_pos⟩ :=
    PanelHingeFramework.exists_generalPosition_polynomial (k := 2) G ends
  have hQgpne : Qgp ≠ 0 := by
    obtain ⟨f, hf⟩ := Countable.exists_injective_nat α
    refine fun h => hQgp_ne (fun a => (f a : ℝ)) ?_ (by rw [h, map_zero])
    exact fun a b hab => hf (Nat.cast_injective hab)
  obtain ⟨q₀, _, halg⟩ := exists_injective_algebraicIndependent_real (α × Fin (2 + 2))
  have hq₀gp : MvPolynomial.eval q₀ Qgp ≠ 0 :=
    MvPolynomial.eval_ne_zero_of_coeffs_subset_range_of_algebraicIndependent halg hQgprat hQgpne
  have hgp : (PanelHingeFramework.ofNormals (k := 2) G ends q₀).IsGeneralPosition :=
    hQgp_pos q₀ hq₀gp
  set F := (PanelHingeFramework.ofNormals (k := 2) G ends q₀).toBodyHinge with hF
  have hFg : F.graph = G := rfl
  -- `rigidityRows F = ∅` (no links), so `span = ⊥` and `finrank = 0`.
  have hrows : F.rigidityRows = ∅ := by
    ext φ; simp only [Set.mem_empty_iff_false, iff_false]
    rintro ⟨e, u, v, hlink, _⟩
    exact hnoLink e u v (hFg ▸ hlink)
  have hfinrank : Module.finrank ℝ (Submodule.span ℝ F.rigidityRows) = 0 := by
    rw [hrows, Submodule.span_empty, finrank_bot]
  refine ⟨PanelHingeFramework.ofNormals (k := 2) G ends q₀,
    PanelHingeFramework.ofNormals_graph G ends q₀, hgp, ?_, ?_, halg⟩
  · -- Rank conjunct: target = 0.
    have hdef : (G.deficiency n : ℤ) = (Graph.bodyBarDim n : ℤ) * ((V(G).ncard : ℤ) - 1) := hG.1
    rw [← hF, hfinrank, hdef, hn]
    push_cast
    ring
  · -- Link-recording: vacuous since `E(G) = ∅`.
    intro e u v hlink
    exact absurd hlink (hnoLink e u v)

/-- **Theorem 5.5 base producer, single-edge arm — general-position form** (`lem:theorem-55-base`;
`hbase` carry's GP conjunct, the one base arm where the GP conjunct does real work, Phase 22i L3b).
The GP-conjunct companion of `theorem_55_base_producer_single_edge`: a *simple* minimal-`1`-dof
graph `G` with `V(G) = {x, y}` (`x ≠ y`) and `E(G) = {e}` (a single hinge joining distinct bodies,
trichotomy arm (ii)) carries a *generic* full-rank panel realization
(`HasGenericFullRankRealization`) at rank `D(|V|−1) − def = D·1 − 1 = D − 1 = 5` (at `d = 3`).

The genuine GP construction: the framework `ofNormals G ends q₀` (with `ends := fun _ => (x, y)`)
is built at an injective algebraically-independent seed `q₀`
(`exists_injective_algebraicIndependent_real`), a non-root of the general-position polynomial
(`exists_generalPosition_polynomial`). General position forces the single hinge's supporting
extensor nonzero (`supportExtensor_ne_zero_of_isGeneralPosition`, since `x ≠ y`), and the
single-hinge-row block has rank `D − 1` (`span_panelRow_linking_eq_rigidityRows` +
`finrank_span_panelRow_edge`). Link-recording holds since every link is at `e = xy` and `ends e =
(x, y)`. -/
theorem theorem_55_base_producer_single_edge_gp [DecidableEq β] [Finite α] [Finite β] {n : ℕ}
    (G : Graph α β) {x y : α} {e : β}
    (hxy : x ≠ y) (hVG : V(G) = {x, y}) (hEG : E(G) = {e})
    (hl : G.IsLink e x y) (hG : G.IsMinimalKDof n 1) :
    PanelHingeFramework.HasGenericFullRankRealization 2 n G := by
  classical
  set ends : β → α × α := fun _ => (x, y) with hends_def
  -- The general-position polynomial and an algebraically-independent injective seed `q₀`.
  obtain ⟨Qgp, hQgp_ne, hQgprat, hQgp_pos⟩ :=
    PanelHingeFramework.exists_generalPosition_polynomial (k := 2) G ends
  have hQgpne : Qgp ≠ 0 := by
    obtain ⟨f, hf⟩ := Countable.exists_injective_nat α
    refine fun h => hQgp_ne (fun a => (f a : ℝ)) ?_ (by rw [h, map_zero])
    exact fun a b hab => hf (Nat.cast_injective hab)
  obtain ⟨q₀, _, halg⟩ := exists_injective_algebraicIndependent_real (α × Fin (2 + 2))
  have hq₀gp : MvPolynomial.eval q₀ Qgp ≠ 0 :=
    MvPolynomial.eval_ne_zero_of_coeffs_subset_range_of_algebraicIndependent halg hQgprat hQgpne
  have hgp : (PanelHingeFramework.ofNormals (k := 2) G ends q₀).IsGeneralPosition :=
    hQgp_pos q₀ hq₀gp
  set Q := PanelHingeFramework.ofNormals (k := 2) G ends q₀ with hQ
  set F := Q.toBodyHinge with hF
  have hFg : F.graph = G := rfl
  -- Every link uses edge `e` (the only edge, `E(G) = {e}`).
  have hlink_e : ∀ e' u v, G.IsLink e' u v → e' = e := by
    intro e' u v he'
    have := he'.edge_mem; rw [hEG] at this
    exact Set.mem_singleton_iff.mp this
  -- The vertex set has ncard 2.
  have hVcard : V(G).ncard = 2 := by rw [hVG, Set.ncard_pair hxy]
  -- The single edge `e` has `ends e = (x, y)` with `x ≠ y`, so its supporting extensor is nonzero
  -- (general position).
  have hQends : Q.ends = ends := by rw [hQ]; exact PanelHingeFramework.ofNormals_ends G ends q₀
  have hFe_ne : F.supportExtensor e ≠ 0 := by
    rw [hF]
    exact Q.supportExtensor_ne_zero_of_isGeneralPosition hgp (by rw [hQends, hends_def]; exact hxy)
  -- Link-recording: every link is at `e`, with selector `ends e = (x, y)`.
  have hrec : ∀ e' u v, G.IsLink e' u v →
      ((Q.ends e').1 = u ∧ (Q.ends e').2 = v) ∨ ((Q.ends e').1 = v ∧ (Q.ends e').2 = u) := by
    intro e' u v he'
    have he'e : e' = e := hlink_e e' u v he'
    subst he'e
    rw [hQends, hends_def]
    exact hl.eq_and_eq_or_eq_and_eq he'
  refine ⟨Q, PanelHingeFramework.ofNormals_graph G ends q₀, hgp, ?_, hrec, halg⟩
  -- Rank conjunct: `finrank (span rigidityRows) = D − 1 = D·1 − 1`.
  have hends : ∀ e' u v, F.graph.IsLink e' u v →
      F.graph.IsLink e' (ends e').1 (ends e').2 := by
    intro e' u v he'
    rw [hends_def]
    exact (hlink_e e' u v (hFg ▸ he')).symm ▸ (hFg ▸ hl)
  have hne_link : ∀ e', F.graph.IsLink e' (ends e').1 (ends e').2 →
      F.supportExtensor e' ≠ 0 := by
    intro e' he'
    have he'e : e' = e := hlink_e e' x y (hFg ▸ (by simpa [hends_def] using he'))
    subst he'e
    exact hFe_ne
  rw [← F.span_panelRow_linking_eq_rigidityRows hends hne_link]
  -- The linking subtype is exactly the `e`-rows (the only link is `e`).
  have hrange : Set.range (fun i : {i : β × Set.powersetCard (Fin 4) 2
        × Set.powersetCard (Fin 4) 2 //
          F.graph.IsLink i.1 (ends i.1).1 (ends i.1).2} => F.panelRow ends i.val)
      = Set.range (fun p : Set.powersetCard (Fin 4) 2
          × Set.powersetCard (Fin 4) 2 => F.panelRow ends (e, p.1, p.2)) := by
    ext φ; simp only [Set.mem_range]
    constructor
    · rintro ⟨⟨⟨e', t₁, t₂⟩, hlink⟩, rfl⟩
      have he'e : e' = e := hlink_e e' x y (hFg ▸ by simpa [hends_def] using hlink)
      exact ⟨(t₁, t₂), by simp [he'e]⟩
    · rintro ⟨⟨t₁, t₂⟩, rfl⟩
      exact ⟨⟨(e, t₁, t₂), by simpa [hends_def, hFg] using hl⟩, rfl⟩
  conv_lhs => rw [hrange]
  rw [F.finrank_span_panelRow_edge (huv := by simp [hends_def, hxy])
      (hne := by simpa [hends_def] using hFe_ne)]
  -- Target: `screwDim 2 * (ncard - 1 : ℤ) - deficiency n = screwDim 2 - 1`.
  have hdef : (G.deficiency n : ℤ) = 1 := hG.1
  rw [Nat.cast_sub (by decide : 1 ≤ screwDim 2)]
  push_cast [hVcard, hdef]
  ring

/-- **Theorem 5.5 base producer, trichotomy dispatch** (`lem:theorem-55-base-producer`;
`hbase` carry, Phase 22i L3b). For a minimal-`k`-dof-graph `G` with `|V(G)| ≤ 2` (the base
region of `minimal_kdof_reduction_all_k`), the **conditioned pair**
`(G.Simple → HasGenericFullRankRealization 2 n G) ∧ HasPanelRealization 2 n G` — the L9 spine's
conditioned motive `Pc G` (`def:rank-hypothesis`, M3 + M2) — holds.

Dispatches via `isMinimalKDof_ncard_le_two_trichotomy` to the L3b arm lemmas. The bare
`HasPanelRealization` conjunct (the `.2`) comes from the three bare arms; the conditioned
`G.Simple → HasGenericFullRankRealization` conjunct (the `.1`) from the GP arms (the empty and
single-edge GP arms do the real work, the parallel-pair arm is vacuous by simplicity):
* **(i) empty arm** (`E(G) = ∅`): the all-zero framework, rank 0 —
  `theorem_55_base_producer_empty` (bare) / `theorem_55_base_producer_empty_gp` (the
  single-body / empty GP framework at the alg-indep seed).
* **(ii) single-edge arm** (`|V| = 2`, `|E| = 1`): rank `D − 1` —
  `theorem_55_base_producer_single_edge` (bare, one nonzero extensor in `n₀^⊥`) /
  `theorem_55_base_producer_single_edge_gp` (the genuine `def = 1 > 0` GP realization at the
  alg-indep seed — the one base arm where the GP conjunct does real work).
* **(iii) parallel-pair arm** (`|V| = 2`, `|E| = 2`, `k = 0`): coincident panels + two LI
  extensors, rank `D` — `theorem_55_base_producer_parallel_pair` (bare). GP conjunct: `G` cannot
  be simple (`not_simple_of_isMinimalKDof_of_ncard_two`), so the `G.Simple →` antecedent is
  vacuous.

The `hn : bodyBarDim n = screwDim 2` hypothesis threads the `d = 3` / `n = 3` constraint
into the empty arms' rank arithmetic (the empty arm's rank target needs the
`deficiency = bodyBarDim n * (|V| − 1) = screwDim 2 * (|V| − 1)` equality). -/
theorem theorem_55_base_producer [DecidableEq β] [Finite α] [Finite β] {n : ℕ}
    (hD : 2 ≤ Graph.bodyBarDim n) (hn : Graph.bodyBarDim n = screwDim 2)
    {k : ℤ} (G : Graph α β) (hG : G.IsMinimalKDof n k)
    (hne : V(G).Nonempty) (hV : V(G).ncard ≤ 2) :
    (G.Simple → PanelHingeFramework.HasGenericFullRankRealization 2 n G) ∧
      HasPanelRealization 2 n G := by
  rcases Graph.isMinimalKDof_ncard_le_two_trichotomy hD hG hne hV with
    ⟨hE, hk⟩ | ⟨x, y, e, hxy, hVG, hEG, hl, hk⟩ | ⟨x, y, e, f, hxy, hef, hVG, hEG, hle, hlf, hk⟩
  · -- (i) empty arm: `E(G) = ∅`, `k = bodyBarDim n * (ncard - 1)`.
    -- Bare: all-zero framework, rank 0. GP (when `G.Simple`): empty GP framework at the seed.
    exact ⟨fun _ => theorem_55_base_producer_empty_gp hn G hE hne (hk ▸ hG),
      theorem_55_base_producer_empty hn G hE (hk ▸ hG)⟩
  · -- (ii) single-edge arm: `|V| = 2`, `|E| = 1`, `G.IsLink e x y`, `k = 1`.
    -- Bare: one nonzero extensor, rank `D − 1`. GP (when `G.Simple`): the genuine `def = 1` GP
    -- realization at the alg-indep seed.
    exact ⟨fun _ => theorem_55_base_producer_single_edge_gp G hxy hVG hEG hl (hk ▸ hG),
      theorem_55_base_producer_single_edge G hxy hVG hEG hl (hk ▸ hG)⟩
  · -- (iii) parallel-pair arm: `|V| = 2`, `|E| = {e,f}`, `k = 0`.
    -- `G` is not simple (two parallel edges between the same pair), so the GP conjunct is vacuous.
    have hVcard : V(G).ncard = 2 := by rw [hVG, Set.ncard_pair hxy]
    have hnotSimple : ¬ G.Simple :=
      Graph.not_simple_of_isMinimalKDof_of_ncard_two (by omega) (hk ▸ hG) hVcard
    -- `G.deficiency n = 0` from `IsMinimalKDof n k` and `k = 0`.
    have hdef : G.deficiency n = 0 := by exact_mod_cast hG.1.trans hk
    have hprod := theorem_55_base_producer_parallel_pair G hxy hef hVG hEG hle hlf hdef
    exact ⟨fun hSimple => absurd hSimple hnotSimple, hprod⟩

/-- **Theorem 5.5 at `d = 3`, full conditioned-motive form, green-modulo-{`h622`,`h65`,
`hsplit`,`hcontract`}** (`thm:theorem-55`, the `n`-parameter-`d = 3` instance over the
(β)-shape reduction; Katoh–Tanigawa 2011 Theorem 5.5, §6.4.1, Phase 22h L5c′).

Instantiates `theorem_55_generic` at `k = 2` with the `hsplitGP` slot wired to
`case_III_realization`; `hbaseGP` is discharged via `not_simple_of_isMinimalKDof_of_ncard_two`
(a simple two-vertex minimal-`0`-dof graph does not exist, KT p. 671 case (iii)); the bare
`hbase` slot is now discharged by `theorem_55_base_producer` (Phase 22i L3b dispatch).

The `hcontractGP` slot is discharged by the **KT 6.3-vs-6.5 dispatch** (Phase 22h L5c′):
by classical cases on whether some proper rigid subgraph `H` of `G` has a simple contraction
`G.rigidContract H r` (KT Lemma 6.3 / Lemma 6.5 dichotomy at p. 673).
- **Positive (KT Lemma 6.3 arm):** extract `(H, r, hcSimple)` and apply `case_I_realization`.
- **Negative (KT Lemma 6.5 arm, unformalized):** carried as the explicit `h65` hypothesis
  (the 6.5-stratum instance; adjudicated carry; Lemma-6.5 arm lands in successor sub-phase 22i).

Conclusion is the **full conditioned pair** `(G.Simple → GP) ∧ HasPanelRealization 2 n G` —
`hbase` discharged; `hsplit`/`hcontract` and `h622`/`h65` remain as named hypotheses
(adjudicated carries; discharged at the 22i all-`k` restructure per
`notes/Phase22h.md` *Blockers*). -/
theorem PanelHingeFramework.theorem_55_d3 [DecidableEq β] [Finite α] [Finite β] {n : ℕ}
    (hD : 6 ≤ Graph.bodyBarDim n)
    -- `hn` threads the `d = 3` / `D = screwDim 2 = 6` constraint into the base producer's
    -- empty-arm rank arithmetic (needed by `theorem_55_base_producer`).
    (hn : Graph.bodyBarDim n = screwDim 2)
    (hfresh : ∀ G' : Graph α β, ∃ e₀ : β, e₀ ∉ E(G'))
    (hsplit : ∀ G : Graph α β, G.IsMinimalKDof n 0 → 3 ≤ V(G).ncard →
      (∀ H : Graph α β, ¬ H.IsProperRigidSubgraph G n) →
      (∀ G' : Graph α β, G'.IsMinimalKDof n 0 → 2 ≤ V(G').ncard →
        V(G').ncard < V(G).ncard → HasPanelRealization 2 n G') →
      HasPanelRealization 2 n G)
    (hcontract : ∀ G : Graph α β, G.IsMinimalKDof n 0 → 3 ≤ V(G).ncard →
      (∃ H : Graph α β, H.IsProperRigidSubgraph G n) →
      (∀ G' : Graph α β, G'.IsMinimalKDof n 0 → 2 ≤ V(G').ncard →
        V(G').ncard < V(G).ncard → HasPanelRealization 2 n G') →
      HasPanelRealization 2 n G)
    -- GAP 6 (adjudicated carry, §1.50(b) option (ii)): the eq.-(6.22) nested-IH rank bound,
    -- quantified over the graph, chain vertices/edges, and the IH-suppliable (ends, q) data.
    -- Instantiated at each `(G, v, a, b, e₀)` invocation inside the `hsplitGP` wiring.
    (h622 : ∀ (G : Graph α β) (v a b : α) (e₀ : β)
        (ends : β → α × α) (q : α × Fin 4 → ℝ),
      (∀ e u w, (G.splitOff v a b e₀).IsLink e u w → ends e = (u, w) ∨ ends e = (w, u)) →
      (∀ x y : α, x ≠ y → LinearIndependent ℝ ![fun i => q (x, i), fun i => q (y, i)]) →
      AlgebraicIndependent ℚ q →
      screwDim 2 * (V(G.splitOff v a b e₀).ncard - 1) - (screwDim 2 - 2)
        ≤ Module.finrank ℝ (Submodule.span ℝ
            (PanelHingeFramework.ofNormals (G.removeVertex v) ends
              q).toBodyHinge.rigidityRows))
    -- GAP 5 / h65 (adjudicated carry): KT Lemma 6.5 arm — every proper rigid subgraph of `G`
    -- has non-simple contraction; discharged in successor sub-phase 22i alongside the all-`k`
    -- motive restructure.  Quantified form: for each `G` in the induction, given `G.Simple` and
    -- the evidence that every `IsProperRigidSubgraph`'s contraction is non-simple, produce the
    -- generic realization.  (`\uses{lem:case-I-dispatch}` in the blueprint instance node.)
    (h65 : ∀ G : Graph α β, G.IsMinimalKDof n 0 → 3 ≤ V(G).ncard →
      (∃ H : Graph α β, H.IsProperRigidSubgraph G n) → G.Simple →
      (∀ H : Graph α β, H.IsProperRigidSubgraph G n → ∀ r ∈ V(H),
          ¬ (G.rigidContract H r).Simple) →
      (∀ G' : Graph α β, G'.IsMinimalKDof n 0 → 2 ≤ V(G').ncard →
        V(G').ncard < V(G).ncard →
        (G'.Simple → PanelHingeFramework.HasGenericFullRankRealization 2 n G') ∧
          HasPanelRealization 2 n G') →
      PanelHingeFramework.HasGenericFullRankRealization 2 n G)
    (G : Graph α β) (hG : G.IsMinimalKDof n 0) (hV : 2 ≤ V(G).ncard) :
    (G.Simple → PanelHingeFramework.HasGenericFullRankRealization 2 n G) ∧
      HasPanelRealization 2 n G :=
  theorem_55_generic
    -- `hbase`: discharged by `theorem_55_base_producer` (Phase 22i L3b dispatch),
    -- taking the `.2` (bare) conjunct of the conditioned pair.
    -- `V(G).Nonempty` from `ncard = 2 ≥ 1`; `ncard ≤ 2` from `ncard = 2`.
    (fun G hG hV2 => by
      have hne : V(G).Nonempty := (Set.ncard_pos (Set.toFinite _)).mp (by omega)
      exact (theorem_55_base_producer (by omega) hn G hG hne (Nat.le_of_eq hV2)).2)
    -- `hbaseGP`: discharged by vacuity — a simple two-vertex minimal-`0`-dof graph
    -- does not exist (`not_simple_of_isMinimalKDof_of_ncard_two`, KT p. 671 case (iii)).
    (fun G hG hV2 hSimple =>
      absurd hSimple (Graph.not_simple_of_isMinimalKDof_of_ncard_two (by omega) hG hV2))
    hsplit
    (fun G hG hV3 hnoRigid hSimple hIH =>
      PanelHingeFramework.case_III_realization hD hfresh h622 G hG hV3 hnoRigid hSimple hIH)
    hcontract
    -- `hcontractGP`: KT 6.3-vs-6.5 dispatch (L5c′). Classical case split on whether some
    -- proper rigid subgraph has a simple contraction.
    (fun G hG hV3 hrig hSimple hIH => by
      by_cases hd : ∃ H : Graph α β, ∃ r : α,
          H.IsProperRigidSubgraph G n ∧ r ∈ V(H) ∧ (G.rigidContract H r).Simple
      · -- KT Lemma 6.3 arm: `(G.rigidContract H r).Simple`; apply `case_I_realization`.
        obtain ⟨H, r, hH, hr, hcSimple⟩ := hd
        exact PanelHingeFramework.case_I_realization (by omega) G hG hH hr hH.2.1 hSimple
          hcSimple hIH
      · -- KT Lemma 6.5 arm (unformalized): carry `h65`.
        exact h65 G hG hV3 hrig hSimple
          (fun H hH r hr hcs => hd ⟨H, r, hH, hr, hcs⟩) hIH)
    G hG hV

/-- **The off-edge selector re-aim** (Phase 22h L5d′ micro-brick): rebuild a panel-hinge framework
with graph `G` and the same panel normals as `Q`, but with an endpoint selector that uses `Q.ends`
on links of `G` and a fixed pair `(x₀, y₀)` on non-links. Since `IsInfinitesimalMotion` fires only
on links, this preserves the motion space; and with `Q.IsGeneralPosition` + `x₀ ≠ y₀`, every
edge's supporting extensor is nonzero. -/
private noncomputable def PanelHingeFramework.reaim (k : ℕ) {α β : Type*}
    (Q : PanelHingeFramework k α β) (G : Graph α β) (x₀ y₀ : α) :
    PanelHingeFramework k α β where
  graph := G
  normal := Q.normal
  ends := fun e =>
    haveI := Classical.propDecidable (∃ u v, G.IsLink e u v)
    if _h : ∃ u v, G.IsLink e u v then Q.ends e else (x₀, y₀)

/-- The `reaim` framework's `toBodyHinge` has the same `infinitesimalMotions` as `Q.toBodyHinge`
(with graph `G`): only link extensors enter the constraint, and `reaim` agrees with `Q` on links. -/
private theorem PanelHingeFramework.reaim_infinitesimalMotions {k : ℕ} {α β : Type*}
    (Q : PanelHingeFramework k α β) (G : Graph α β) (x₀ y₀ : α)
    (hQg : Q.graph = G) :
    (Q.reaim k G x₀ y₀).toBodyHinge.infinitesimalMotions
      = Q.toBodyHinge.infinitesimalMotions := by
  apply (BodyHingeFramework.infinitesimalMotions_eq_of_isLink_supportExtensor
    Q.toBodyHinge (Q.reaim k G x₀ y₀).toBodyHinge (by simp [reaim, hQg]) (fun e u v he => ?_)).symm
  simp only [toBodyHinge_supportExtensor, reaim]
  have : (∃ u' v', G.IsLink e u' v') := ⟨u, v, hQg ▸ he⟩
  simp [this]

/-- **Theorem 5.5 → Proposition 1.1, `def = 0`/simple/spanning stratum**
(`prop:rigidity-matrix-prop11`, the `d = 3` instance; Katoh–Tanigawa 2011 §5.1/§5.2,
Phase 22h L5d′). For a simple spanning
minimal-`0`-dof graph on `≥ 2` bodies in `d = 3`, a generic panel-hinge realization produces
a framework realizing the rank hypothesis at `def(G̃) = 0`: `dim Z(G, Q) = D = D + def(G̃)`.

This is the first genuine `hgen` feed of `rigidityMatrix_prop11` (KT Prop 1.1): the spanning
condition (`hspan : V(G) = Set.univ`) kills the complement so `dim Z = D·1 = D ≤ D + 0`, and the
off-edge selector re-aim (`reaim`) satisfies `hC : ∀ e, supportExtensor e ≠ 0` by GP on links
(link-recording + `IsLink.ne`) and the explicit pair `(x₀, y₀)` on non-links. -/
theorem PanelHingeFramework.rankHypothesis_deficiency_of_theorem_55_d3
    [Nonempty α] [Finite α] [Finite β] [DecidableEq β]
    (G : Graph α β) (hG : G.IsMinimalKDof 3 0) (hV : 2 ≤ V(G).ncard)
    (hspan : V(G) = Set.univ) (_hSimple : G.Simple)
    (hGP : PanelHingeFramework.HasGenericFullRankRealization 2 3 G) :
    ∃ Q : PanelHingeFramework 2 α β, Q.graph = G ∧
      Q.toBodyHinge.RankHypothesis (G.deficiency 3) := by
  haveI : Fintype α := Fintype.ofFinite α
  -- Extract the GP realization.
  obtain ⟨Q, hQg, hQgp, hQrank, hQrec, hQai⟩ := hGP
  -- Derive rigidity from the rank hypothesis.
  have hne : V(G).Nonempty := by rw [hspan]; exact Set.univ_nonempty
  have hne' : Q.toBodyHinge.graph.vertexSet.Nonempty := by
    rw [PanelHingeFramework.toBodyHinge_graph, hQg]; exact hne
  rw [hG.1, sub_zero] at hQrank
  have hVeq : V(G) = Q.toBodyHinge.graph.vertexSet := by
    rw [PanelHingeFramework.toBodyHinge_graph, hQg]
  have h1 : 1 ≤ V(G).ncard := (Set.ncard_pos (Set.toFinite _)).2 hne
  have hQrig : Q.toBodyHinge.IsInfinitesimallyRigidOn V(G) := by
    rw [hVeq, BodyHingeFramework.isInfinitesimallyRigidOn_vertexSet_iff_finrank_span_rigidityRows
        Q.toBodyHinge hne', ← hVeq]
    zify [h1] at hQrank ⊢; exact_mod_cast hQrank
  -- Get two distinct bodies from `2 ≤ V(G).ncard` + `hspan`.
  have hVcard : 2 ≤ Fintype.card α := by
    have : V(G).ncard = Fintype.card α := by
      rw [hspan, Set.ncard_univ, Nat.card_eq_fintype_card]
    omega
  obtain ⟨x₀⟩ := ‹Nonempty α›
  obtain ⟨y₀, hxy⟩ := Fintype.exists_ne_of_one_lt_card (by omega) x₀
  -- Build `Q'` with the re-aimed ends selector.
  let Q' := Q.reaim 2 G x₀ y₀
  -- `Q'` has graph `G`.
  have hQ'g : Q'.graph = G := rfl
  -- `Q'` has the same `infinitesimalMotions` as `Q` (on graph `G`).
  have hmotions : Q'.toBodyHinge.infinitesimalMotions = Q.toBodyHinge.infinitesimalMotions :=
    Q.reaim_infinitesimalMotions G x₀ y₀ hQg
  -- `Q'` is infinitesimally rigid on `V(G)`.
  have hQ'rig : Q'.toBodyHinge.IsInfinitesimallyRigidOn V(G) := by
    intro S hS u hu v hv
    have hS' : Q.toBodyHinge.IsInfinitesimalMotion S :=
      (BodyHingeFramework.mem_infinitesimalMotions Q.toBodyHinge S).mp
        (hmotions ▸ (BodyHingeFramework.mem_infinitesimalMotions Q'.toBodyHinge S).mpr hS)
    exact hQrig S hS' u hu v hv
  -- Looplessness from minimality.
  haveI hloop : G.Loopless := Graph.loopless_of_isMinimalKDof hG
  -- `hC`: every edge's supporting extensor is nonzero.
  have hC : ∀ e, Q'.toBodyHinge.supportExtensor e ≠ 0 := by
    intro e
    simp only [Q', reaim, toBodyHinge_supportExtensor]
    by_cases hlink : ∃ u v, G.IsLink e u v
    · -- Link case: `Q'.ends e = Q.ends e`; use link-recording + looplessness + GP.
      rw [dif_pos hlink]
      obtain ⟨u, v, hle⟩ := hlink
      rw [panelSupportExtensor_ne_zero_iff]
      -- From link-recording: `(Q.ends e) = (u,v)` or `(v,u)`.
      rcases hQrec e u v (hQg ▸ hle) with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2]; exact hQgp u v hle.ne
      · rw [h1, h2]; exact hQgp v u hle.ne.symm
    · -- Non-link case: `Q'.ends e = (x₀, y₀)`.
      rw [dif_neg hlink]
      simp only [panelSupportExtensor_ne_zero_iff]
      exact hQgp x₀ y₀ hxy.symm
  -- Nonemptiness.
  have hQ'ne : V(Q'.toBodyHinge.graph).Nonempty := by
    simp only [toBodyHinge_graph, hQ'g, hspan]
    exact Set.univ_nonempty
  -- Rigidity on the vertex set; needed for `finrank_…_of_isInfinitesimallyRigidOn_vertexSet`.
  have hQ'rig_vs : Q'.toBodyHinge.IsInfinitesimallyRigidOn Q'.toBodyHinge.graph.vertexSet := by
    simp only [toBodyHinge_graph, hQ'g]; exact hQ'rig
  -- `dim Z = D * 1 = D`.
  have hfinrank : Module.finrank ℝ Q'.toBodyHinge.infinitesimalMotions
      = screwDim 2 * ((V(G))ᶜ.ncard + 1) :=
    Q'.toBodyHinge.finrank_infinitesimalMotions_of_isInfinitesimallyRigidOn_vertexSet
      (by simpa [toBodyHinge_graph, hQ'g] using hQ'ne) hQ'rig_vs
  have hcompl : (V(G))ᶜ.ncard = 0 := by
    simp [hspan, Set.compl_univ]
  -- `hgen`: `(dim Z : ℤ) ≤ D + def`.
  have hgen : (Module.finrank ℝ Q'.toBodyHinge.infinitesimalMotions : ℤ)
      ≤ (screwDim 2 : ℤ) + Q'.toBodyHinge.graph.deficiency 3 := by
    rw [hfinrank, hcompl, Nat.zero_add, Nat.mul_one]
    simp only [toBodyHinge_graph, hQ'g]
    have hdef : G.deficiency 3 = 0 := hG.1
    linarith [hdef.symm ▸ (le_refl (0 : ℤ))]
  -- Apply `rigidityMatrix_prop11`.
  have hprop11 : Q'.toBodyHinge.RankHypothesis (Q'.toBodyHinge.graph.deficiency 3) :=
    rigidityMatrix_prop11 Q'.toBodyHinge 3 (by omega) hC hgen
  exact ⟨Q', hQ'g, by simpa [toBodyHinge_graph, hQ'g] using hprop11⟩

-- ── Auxiliary: side-membership from an induce-IsLink witness ──────────────────────────────
-- Given `G.IsLink e u v` and `(G.induce V₁).IsLink e a b`, conclude `u ∈ V₁` and `v ∈ V₁`.
-- Proof: `eq_or_eq_of_isLink_of_isLink` gives `u = a ∨ u = b`; both options land in V₁.
private lemma mem_V₁_of_induce_isLink_left {α β : Type*} {G : Graph α β} {V₁ : Set α}
    {e : β} {u v a b : α} (hl : G.IsLink e u v) (hl₁ : (G.induce V₁).IsLink e a b) :
    u ∈ V₁ :=
  (G.eq_or_eq_of_isLink_of_isLink hl hl₁.1).elim (· ▸ hl₁.2.1) (· ▸ hl₁.2.2)

private lemma mem_V₁_of_induce_isLink_right {α β : Type*} {G : Graph α β} {V₁ : Set α}
    {e : β} {u v a b : α} (hl : G.IsLink e u v) (hl₁ : (G.induce V₁).IsLink e a b) :
    v ∈ V₁ :=
  (G.eq_or_eq_of_isLink_of_isLink hl.symm hl₁.1).elim (· ▸ hl₁.2.1) (· ▸ hl₁.2.2)

set_option maxHeartbeats 400000 in
-- The |C|=1 subcase builds a large local context that exhausts the default 200000 limit.
/-- **L4a bare-conjunct producer: cut-edge case** (`lem:case-cut-edge-realization`,
bare conjunct; Katoh–Tanigawa 2011 §6.1, Lemma 6.1, the `not-2EC` branch; Phase 22i).

Given a minimal `k`-dof-graph `G` with `|V(G)| ≥ 3` that is not 2-edge-connected, the
bare panel-realization conjunct `HasPanelRealization 2 n G` holds.

**Proof sketch.** `exists_cut_decomposition_of_not_twoEdgeConnected` yields a cut
`V₁ ⊔ V₂ = V(G)`, `|cutEdges G V₁| ≤ 1`, and `k = k₁ + k₂ + D - (D-1)|C|`. Apply the
IH on each induced side. Assemble framework `F` with `supportExtensor` equal to `F₁`'s on
edges inside `V₁`, `F₂`'s on edges inside `V₂`, and a nonzero element `C_cut` of
`normal(u₀)^⊥ ∩ normal(v₀)^⊥` (from `exists_extensor_in_two_panels`) on any cut edge.
Rank lower bound: `le_finrank_span_rigidityRows_of_cut` + IH ranks. Rank upper bound: B2.
The L1e arithmetic `k = k₁ + k₂ + D - (D-1)|C|` + `|V| = |V₁| + |V₂|` closes equality. -/
theorem case_cut_edge_realization [DecidableEq β] [Finite α] [Finite β] {n : ℕ}
    (hD : 2 ≤ Graph.bodyBarDim n) (hn : Graph.bodyBarDim n = screwDim 2)
    {k : ℤ} (G : Graph α β) (hG : G.IsMinimalKDof n k) (_hV3 : 3 ≤ V(G).ncard)
    (hntec : ¬ G.TwoEdgeConnected)
    (hIH : ∀ (k' : ℤ) (G' : Graph α β), G'.IsMinimalKDof n k' → V(G').Nonempty →
      V(G').ncard < V(G).ncard → HasPanelRealization 2 n G') :
    HasPanelRealization 2 n G := by
  classical
  -- ── Step 1: Cut decomposition ─────────────────────────────────────────────────────────
  obtain ⟨V₁, k₁, k₂, hV₁ne, hV₁sub, hV₂ne, hG₁, hG₂, hcut_le, hk_eq⟩ :=
    Graph.exists_cut_decomposition_of_not_twoEdgeConnected (by omega) hG hntec
  -- V₂ = V(G) \ V₁.  V(G.induce V₁) = V₁ definitionally.
  set V₂ := V(G) \ V₁
  -- ── Step 2: IH on each side ────────────────────────────────────────────────────────────
  have hV₁ncard : V(G.induce V₁).ncard < V(G).ncard :=
    Set.ncard_lt_ncard hV₁sub (Set.toFinite _)
  -- Vertex partition: V₁ ⊔ V₂ = V(G), both nonempty.
  have hVcard : V₁.ncard + V₂.ncard = V(G).ncard := by
    have hunion : V₁ ∪ V₂ = V(G) := Set.union_diff_cancel hV₁sub.subset
    have hdisj : Disjoint V₁ V₂ := Set.disjoint_sdiff_right
    rw [← hunion, Set.ncard_union_eq hdisj (Set.toFinite V₁) (Set.toFinite V₂)]
  have hVeq₁ : V(G.induce V₁).ncard = V₁.ncard := rfl
  have hVeq₂ : V(G.induce V₂).ncard = V₂.ncard := rfl
  have hV₂ncard : V(G.induce V₂).ncard < V(G).ncard := by
    have hV₁pos : 0 < V₁.ncard := hV₁ne.ncard_pos
    omega
  obtain ⟨F₁, normal₁, hF₁g, hF₁ne, hF₁ext, hF₁rank⟩ :=
    hIH k₁ (G.induce V₁) hG₁ hV₁ne hV₁ncard
  obtain ⟨F₂, normal₂, hF₂g, hF₂ne, hF₂ext, hF₂rank⟩ :=
    hIH k₂ (G.induce V₂) hG₂ hV₂ne hV₂ncard
  -- ── Step 3: Assemble F ────────────────────────────────────────────────────────────────
  -- Pick a representative vertex from each side (for the normal junk value on off-V(G) verts).
  obtain ⟨u₀, hu₀⟩ := hV₁ne
  -- Normal: use side IH normals; off-V(G) vertices get normal₁ u₀ as junk.
  set normal : α → Fin 4 → ℝ := fun v =>
    if v ∈ V₁ then normal₁ v
    else if v ∈ V₂ then normal₂ v
    else normal₁ u₀
  -- Case-split on whether there are cut edges (at most one, by hcut_le).
  -- In the nonempty case we name its unique endpoints u_c ∈ V₁, v_c ∈ V₂.
  -- In the empty case there are no cut edges so the third branch of extF is vacuous.
  rcases Set.eq_empty_or_nonempty (G.cutEdges V₁) with hC0 | ⟨e_c, he_c⟩
  · -- ── Case |C| = 0 ─────────────────────────────────────────────────────────────────
    -- No cut edges: every graph edge is within V₁ or within V₂.
    set extF : β → ScrewSpace 2 := fun e =>
      if ∃ a b, (G.induce V₁).IsLink e a b then F₁.supportExtensor e
      else if ∃ a b, (G.induce V₂).IsLink e a b then F₂.supportExtensor e
      else (exists_extensor_in_two_panels (normal₁ u₀) (normal₁ u₀)).choose
    set F : BodyHingeFramework 2 α β := ⟨G, extF⟩
    have hlinks : ∀ e u v, G.IsLink e u v → F.supportExtensor e ≠ 0 ∧
        ExtensorInPanel (F.supportExtensor e) (normal u) ∧
        ExtensorInPanel (F.supportExtensor e) (normal v) := by
      intro e u v hl
      simp only [F, extF]
      by_cases hE₁ : ∃ a b, (G.induce V₁).IsLink e a b
      · simp only [hE₁, ↓reduceIte]
        obtain ⟨a, b, hlab⟩ := hE₁
        have hu₁ : u ∈ V₁ := mem_V₁_of_induce_isLink_left hl hlab
        have hv₁ : v ∈ V₁ := mem_V₁_of_induce_isLink_right hl hlab
        simp only [normal, hu₁, hv₁, ↓reduceIte]
        exact hF₁ext e u v (hF₁g ▸ (Graph.induce_isLink G V₁ e u v).mpr ⟨hl, hu₁, hv₁⟩)
      · by_cases hE₂ : ∃ a b, (G.induce V₂).IsLink e a b
        · simp only [hE₁, hE₂, ↓reduceIte]
          obtain ⟨a, b, hlab⟩ := hE₂
          have hu₂ : u ∈ V₂ := mem_V₁_of_induce_isLink_left hl hlab
          have hv₂ : v ∈ V₂ := mem_V₁_of_induce_isLink_right hl hlab
          simp only [normal, hu₂.2, hv₂.2, ↓reduceIte, hu₂, hv₂]
          exact hF₂ext e u v (hF₂g ▸ (Graph.induce_isLink G V₂ e u v).mpr ⟨hl, hu₂, hv₂⟩)
        · -- e is not in E₁ or E₂. Since hC0 says no cut edges, e cannot be a G-edge
          -- crossing V₁/V₂; but hl proves it IS a G-edge, so it must be in E₁ or E₂.
          exfalso
          have hu_V := hl.left_mem; have hv_V := hl.right_mem
          have hu₁_or_hv₁ : u ∈ V₁ ∨ u ∉ V₁ := em _
          by_cases hu₁ : u ∈ V₁
          · by_cases hv₁ : v ∈ V₁
            · exact hE₁ ⟨u, v, (Graph.induce_isLink G V₁ e u v).mpr ⟨hl, hu₁, hv₁⟩⟩
            · -- e is a cut edge (u ∈ V₁, v ∉ V₁), contradicting hC0.
              have hmem : e ∈ G.cutEdges V₁ := by
                simp only [Graph.cutEdges, Set.mem_setOf_eq]
                exact ⟨hl.edge_mem, u, v, hl, hu₁, hv₁⟩
              simp [hC0] at hmem
          · by_cases hv₁ : v ∈ V₁
            · -- e is a cut edge (v ∈ V₁, u ∉ V₁), i.e. hl.symm witnesses it.
              have hmem : e ∈ G.cutEdges V₁ := by
                simp only [Graph.cutEdges, Set.mem_setOf_eq]
                exact ⟨hl.edge_mem, v, u, hl.symm, hv₁, hu₁⟩
              simp [hC0] at hmem
            · exact hE₂ ⟨u, v, (Graph.induce_isLink G V₂ e u v).mpr
                ⟨hl, ⟨hu_V, hu₁⟩, ⟨hv_V, hv₁⟩⟩⟩
    -- Continue with hlinks for Case |C| = 0.
    -- (hlinks proved, now re-establish the span equalities and rank arithmetic identically.)
    have hF₁span : Submodule.span ℝ
        (⟨G.induce V₁, extF⟩ : BodyHingeFramework 2 α β).rigidityRows
        = Submodule.span ℝ F₁.rigidityRows := by
      congr 1; ext φ
      simp only [BodyHingeFramework.rigidityRows, Set.mem_setOf_eq]
      constructor
      · rintro ⟨e, u, v, hl₁, r, hr, rfl⟩
        refine ⟨e, u, v, hF₁g ▸ hl₁, r, ?_, rfl⟩
        simp only [BodyHingeFramework.hingeRowBlock, extF,
          show (∃ a b, (G.induce V₁).IsLink e a b) from ⟨u, v, hl₁⟩, ↓reduceIte] at hr
        simpa [BodyHingeFramework.hingeRowBlock] using hr
      · rintro ⟨e, u, v, hl₁, r, hr, rfl⟩
        have hl₁' : (G.induce V₁).IsLink e u v := hF₁g ▸ hl₁
        refine ⟨e, u, v, hl₁', r, ?_, rfl⟩
        simp only [BodyHingeFramework.hingeRowBlock, extF,
          show (∃ a b, (G.induce V₁).IsLink e a b) from ⟨u, v, hl₁'⟩, ↓reduceIte]
        simpa [BodyHingeFramework.hingeRowBlock] using hr
    have hF₂span : Submodule.span ℝ
        (⟨G.induce V₂, extF⟩ : BodyHingeFramework 2 α β).rigidityRows
        = Submodule.span ℝ F₂.rigidityRows := by
      congr 1; ext φ
      simp only [BodyHingeFramework.rigidityRows, Set.mem_setOf_eq]
      constructor
      · rintro ⟨e, u, v, hl₂, r, hr, rfl⟩
        refine ⟨e, u, v, hF₂g ▸ hl₂, r, ?_, rfl⟩
        have hnotE₁ : ¬ ∃ a b, (G.induce V₁).IsLink e a b :=
          fun ⟨a, b, hlab⟩ => absurd (mem_V₁_of_induce_isLink_left hl₂.1 hlab) hl₂.2.1.2
        simp only [BodyHingeFramework.hingeRowBlock, extF, hnotE₁, ↓reduceIte,
          show (∃ a b, (G.induce V₂).IsLink e a b) from ⟨u, v, hl₂⟩] at hr
        simpa [BodyHingeFramework.hingeRowBlock] using hr
      · rintro ⟨e, u, v, hl₂, r, hr, rfl⟩
        have hl₂' : (G.induce V₂).IsLink e u v := hF₂g ▸ hl₂
        have hnotE₁ : ¬ ∃ a b, (G.induce V₁).IsLink e a b :=
          fun ⟨a, b, hlab⟩ => absurd (mem_V₁_of_induce_isLink_left hl₂'.1 hlab) hl₂'.2.1.2
        refine ⟨e, u, v, hl₂', r, ?_, rfl⟩
        simp only [BodyHingeFramework.hingeRowBlock, extF, hnotE₁, ↓reduceIte,
          show (∃ a b, (G.induce V₂).IsLink e a b) from ⟨u, v, hl₂'⟩] at hr ⊢
        exact hr
    have hFext : ∀ e u v, F.graph.IsLink e u v → F.supportExtensor e ≠ 0 :=
      fun e u v hl => (hlinks e u v hl).1
    have hFE₁ : ∀ e u v, F.graph.IsLink e u v → e ∉ G.cutEdges V₁ →
        u ∈ V₁ ∧ v ∈ V₁ ∨ u ∉ V₁ ∧ v ∉ V₁ := by
      intro e u v hl hnotcut
      simp only [Graph.cutEdges, not_and, Set.mem_setOf_eq] at hnotcut
      by_cases hu₁ : u ∈ V₁
      · left; refine ⟨hu₁, ?_⟩
        by_contra hv₁
        exact (hnotcut hl.edge_mem) ⟨u, v, hl, hu₁, hv₁⟩
      · right; refine ⟨hu₁, ?_⟩
        by_contra hv₁
        exact (hnotcut hl.edge_mem) ⟨v, u, hl.symm, hv₁, hu₁⟩
    have hFcut : ∀ e ∈ G.cutEdges V₁, ∃ a b, F.graph.IsLink e a b ∧ a ∈ V₁ ∧ b ∉ V₁ := by
      intro e he; simp [hC0] at he
    have hbrick := BodyHingeFramework.le_finrank_span_rigidityRows_of_cut F hcut_le hFext
      (fun e u v hl he => hFE₁ e u v hl he) hFcut
    rw [hF₁span, hF₂span] at hbrick
    have hrank₁ : (Module.finrank ℝ (Submodule.span ℝ F₁.rigidityRows) : ℤ)
        = screwDim 2 * ((V₁.ncard : ℤ) - 1) - k₁ := by
      rw [hVeq₁] at hF₁rank; rw [hF₁rank, hG₁.1]
    have hrank₂ : (Module.finrank ℝ (Submodule.span ℝ F₂.rigidityRows) : ℤ)
        = screwDim 2 * ((V₂.ncard : ℤ) - 1) - k₂ := by
      rw [hVeq₂] at hF₂rank; rw [hF₂rank, hG₂.1]
    have hFVne : V(F.graph).Nonempty := ⟨u₀, hV₁sub.subset hu₀⟩
    have hB2 := F.finrank_span_rigidityRows_add_deficiency_le hn hFVne hFext
    have hB2' : (Module.finrank ℝ (Submodule.span ℝ F.rigidityRows) : ℤ)
        ≤ screwDim 2 * ((V(G).ncard : ℤ) - 1) - k := by
      have := hB2; rw [hG.1] at this; linarith
    have hlb : screwDim 2 * ((V(G).ncard : ℤ) - 1) - k ≤
        (Module.finrank ℝ (Submodule.span ℝ F.rigidityRows) : ℤ) := by
      have hbrickZ : (Module.finrank ℝ (Submodule.span ℝ F₁.rigidityRows) : ℤ) +
          (screwDim 2 - 1) * (G.cutEdges V₁).ncard +
          (Module.finrank ℝ (Submodule.span ℝ F₂.rigidityRows) : ℤ) ≤
          (Module.finrank ℝ (Submodule.span ℝ F.rigidityRows) : ℤ) := by exact_mod_cast hbrick
      rw [hrank₁, hrank₂] at hbrickZ
      rw [hn] at hk_eq
      simp only [hC0, Set.ncard_empty] at hbrickZ hk_eq
      have hscrew : 1 ≤ screwDim 2 := by rw [← hn]; omega
      push_cast [Nat.sub_add_cancel hscrew] at hbrickZ hk_eq ⊢
      simp only [mul_zero, add_zero, sub_zero] at hbrickZ hk_eq
      have hVcardZ : (V₁.ncard : ℤ) + V₂.ncard = V(G).ncard := by exact_mod_cast hVcard
      nlinarith
    have hrank_eq : (Module.finrank ℝ (Submodule.span ℝ F.rigidityRows) : ℤ)
        = screwDim 2 * ((V(G).ncard : ℤ) - 1) - k := le_antisymm hB2' hlb
    have hnorm_ne : ∀ v ∈ V(G), normal v ≠ 0 := by
      intro v hv
      simp only [normal]
      by_cases h₁ : v ∈ V₁
      · simp only [h₁, ↓reduceIte]
        exact hF₁ne v h₁
      · have h₂ : v ∈ V₂ := ⟨hv, h₁⟩
        simp only [h₁, ↓reduceIte, h₂]
        exact hF₂ne v h₂
    rw [← hG.1] at hrank_eq
    exact ⟨F, normal, rfl, hnorm_ne, hlinks, hrank_eq⟩
  · -- ── Case |C| = 1 ─────────────────────────────────────────────────────────────────
    -- Extract the unique cut edge's endpoints.
    simp only [Graph.cutEdges, Set.mem_setOf_eq] at he_c
    obtain ⟨_, u_c, v_c, hl_c, hu_c, hv_c⟩ := he_c
    -- The cut-edge count is exactly 1 (at most 1 by hcut_le, at least 1 by he_c nonempty).
    -- Pick C_cut in both endpoint normals.
    obtain ⟨C_cut, hCne, hC_u, hC_v⟩ :=
      exists_extensor_in_two_panels (normal u_c) (normal v_c)
    -- extF: use F₁/F₂ for within-side edges; C_cut for the (unique) cut edge and junk.
    set extF : β → ScrewSpace 2 := fun e =>
      if ∃ a b, (G.induce V₁).IsLink e a b then F₁.supportExtensor e
      else if ∃ a b, (G.induce V₂).IsLink e a b then F₂.supportExtensor e
      else C_cut
    set F : BodyHingeFramework 2 α β := ⟨G, extF⟩
    -- For any cut edge e with G.IsLink e u v, since |C| ≤ 1 and e_c is the unique cut edge,
    -- e = e_c, so the endpoints are {u_c, v_c} up to swap.
    have hec_mem : e_c ∈ G.cutEdges V₁ := by
      simp only [Graph.cutEdges, Set.mem_setOf_eq]
      exact ⟨hl_c.edge_mem, u_c, v_c, hl_c, hu_c, hv_c⟩
    have hcut_uniq : ∀ e u v, G.IsLink e u v → u ∈ V₁ → v ∉ V₁ → e = e_c := by
      intro e u v hle hu hv
      have hmem : e ∈ G.cutEdges V₁ := by
        simp only [Graph.cutEdges, Set.mem_setOf_eq]
        exact ⟨hle.edge_mem, u, v, hle, hu, hv⟩
      -- cutEdges has at most 1 element by hcut_le; e_c is also in cutEdges; so e = e_c.
      exact (Set.ncard_le_one (Set.toFinite _)).mp hcut_le e hmem e_c hec_mem
    have hlinks : ∀ e u v, G.IsLink e u v → F.supportExtensor e ≠ 0 ∧
        ExtensorInPanel (F.supportExtensor e) (normal u) ∧
        ExtensorInPanel (F.supportExtensor e) (normal v) := by
      intro e u v hl
      simp only [F, extF]
      by_cases hE₁ : ∃ a b, (G.induce V₁).IsLink e a b
      · simp only [hE₁, ↓reduceIte]
        obtain ⟨a, b, hlab⟩ := hE₁
        have hu₁ : u ∈ V₁ := mem_V₁_of_induce_isLink_left hl hlab
        have hv₁ : v ∈ V₁ := mem_V₁_of_induce_isLink_right hl hlab
        simp only [normal, hu₁, hv₁, ↓reduceIte]
        exact hF₁ext e u v (hF₁g ▸ (Graph.induce_isLink G V₁ e u v).mpr ⟨hl, hu₁, hv₁⟩)
      · by_cases hE₂ : ∃ a b, (G.induce V₂).IsLink e a b
        · simp only [hE₁, hE₂, ↓reduceIte]
          obtain ⟨a, b, hlab⟩ := hE₂
          have hu₂ : u ∈ V₂ := mem_V₁_of_induce_isLink_left hl hlab
          have hv₂ : v ∈ V₂ := mem_V₁_of_induce_isLink_right hl hlab
          simp only [normal, hu₂.2, hv₂.2, ↓reduceIte, hu₂, hv₂]
          exact hF₂ext e u v (hF₂g ▸ (Graph.induce_isLink G V₂ e u v).mpr ⟨hl, hu₂, hv₂⟩)
        · -- Cut edge. extF e = C_cut. Need C_cut ∈ (normal u)^⊥ ∩ (normal v)^⊥.
          simp only [hE₁, hE₂, ↓reduceIte]
          have hu_V := hl.left_mem; have hv_V := hl.right_mem
          -- Determine sides.
          have hopp : (u ∈ V₁ ∧ v ∈ V₂) ∨ (u ∈ V₂ ∧ v ∈ V₁) := by
            by_cases hu₁ : u ∈ V₁
            · left; refine ⟨hu₁, ?_⟩
              exact ⟨hv_V, fun hv₁ => hE₁ ⟨u, v,
                (Graph.induce_isLink G V₁ e u v).mpr ⟨hl, hu₁, hv₁⟩⟩⟩
            · by_cases hv₁ : v ∈ V₁
              · right; exact ⟨⟨hu_V, hu₁⟩, hv₁⟩
              · exact absurd ⟨u, v, (Graph.induce_isLink G V₂ e u v).mpr
                    ⟨hl, ⟨hu_V, hu₁⟩, ⟨hv_V, hv₁⟩⟩⟩ hE₂
          refine ⟨hCne, ?_, ?_⟩
          · rcases hopp with ⟨hu₁, hv₂⟩ | ⟨hu₂, hv₁⟩
            · -- e = e_c (unique cut edge), and e_c goes u_c → v_c or v_c → u_c.
              have heq : e = e_c := hcut_uniq e u v hl hu₁ hv₂.2
              subst heq
              -- Now endpoints of e_c are {u_c, v_c}; by eq_and_eq_or_eq_and_eq, u ∈ {u_c, v_c}.
              -- hu₁ : u ∈ V₁ and hu_c : u_c ∈ V₁; hC_u : ExtensorInPanel C_cut (normal u_c).
              -- We need ExtensorInPanel C_cut (normal u). By uniqueness, u = u_c or u = v_c.
              -- But hv₂ : v ∈ V₂, hv_c : v_c ∈ V₂, so if u = v_c then u ∈ V₂, contradicting hu₁.
              rcases hl.eq_and_eq_or_eq_and_eq hl_c with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
              · exact hC_u  -- u = u_c: ExtensorInPanel C_cut (normal u_c)
              · exact hC_v  -- u = v_c: ExtensorInPanel C_cut (normal v_c)
            · have heq : e = e_c := hcut_uniq e v u hl.symm hv₁ hu₂.2
              subst heq
              rcases hl.eq_and_eq_or_eq_and_eq hl_c with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
              · exact hC_u  -- u = u_c: ExtensorInPanel C_cut (normal u_c)
              · exact hC_v  -- u = v_c: ExtensorInPanel C_cut (normal v_c)
          · rcases hopp with ⟨hu₁, hv₂⟩ | ⟨hu₂, hv₁⟩
            · have heq : e = e_c := hcut_uniq e u v hl hu₁ hv₂.2
              subst heq
              rcases hl.eq_and_eq_or_eq_and_eq hl_c with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
              · exact hC_v  -- v = v_c: ExtensorInPanel C_cut (normal v_c)
              · exact hC_u  -- v = u_c: ExtensorInPanel C_cut (normal u_c)
            · have heq : e = e_c := hcut_uniq e v u hl.symm hv₁ hu₂.2
              subst heq
              rcases hl.eq_and_eq_or_eq_and_eq hl_c with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
              · exact hC_v  -- v = v_c: ExtensorInPanel C_cut (normal v_c)
              · exact hC_u  -- v = u_c: ExtensorInPanel C_cut (normal u_c)
    -- Continue with hlinks for Case |C| = 1.
    have hF₁span : Submodule.span ℝ
        (⟨G.induce V₁, extF⟩ : BodyHingeFramework 2 α β).rigidityRows
        = Submodule.span ℝ F₁.rigidityRows := by
      congr 1; ext φ
      simp only [BodyHingeFramework.rigidityRows, Set.mem_setOf_eq]
      constructor
      · rintro ⟨e, u, v, hl₁, r, hr, rfl⟩
        refine ⟨e, u, v, hF₁g ▸ hl₁, r, ?_, rfl⟩
        simp only [BodyHingeFramework.hingeRowBlock, extF,
          show (∃ a b, (G.induce V₁).IsLink e a b) from ⟨u, v, hl₁⟩, ↓reduceIte] at hr
        simpa [BodyHingeFramework.hingeRowBlock] using hr
      · rintro ⟨e, u, v, hl₁, r, hr, rfl⟩
        have hl₁' : (G.induce V₁).IsLink e u v := hF₁g ▸ hl₁
        refine ⟨e, u, v, hl₁', r, ?_, rfl⟩
        simp only [BodyHingeFramework.hingeRowBlock, extF,
          show (∃ a b, (G.induce V₁).IsLink e a b) from ⟨u, v, hl₁'⟩, ↓reduceIte]
        simpa [BodyHingeFramework.hingeRowBlock] using hr
    have hF₂span : Submodule.span ℝ
        (⟨G.induce V₂, extF⟩ : BodyHingeFramework 2 α β).rigidityRows
        = Submodule.span ℝ F₂.rigidityRows := by
      congr 1; ext φ
      simp only [BodyHingeFramework.rigidityRows, Set.mem_setOf_eq]
      constructor
      · rintro ⟨e, u, v, hl₂, r, hr, rfl⟩
        refine ⟨e, u, v, hF₂g ▸ hl₂, r, ?_, rfl⟩
        have hnotE₁ : ¬ ∃ a b, (G.induce V₁).IsLink e a b :=
          fun ⟨a, b, hlab⟩ => absurd (mem_V₁_of_induce_isLink_left hl₂.1 hlab) hl₂.2.1.2
        simp only [BodyHingeFramework.hingeRowBlock, extF, hnotE₁, ↓reduceIte,
          show (∃ a b, (G.induce V₂).IsLink e a b) from ⟨u, v, hl₂⟩] at hr
        simpa [BodyHingeFramework.hingeRowBlock] using hr
      · rintro ⟨e, u, v, hl₂, r, hr, rfl⟩
        have hl₂' : (G.induce V₂).IsLink e u v := hF₂g ▸ hl₂
        have hnotE₁ : ¬ ∃ a b, (G.induce V₁).IsLink e a b :=
          fun ⟨a, b, hlab⟩ => absurd (mem_V₁_of_induce_isLink_left hl₂'.1 hlab) hl₂'.2.1.2
        refine ⟨e, u, v, hl₂', r, ?_, rfl⟩
        simp only [BodyHingeFramework.hingeRowBlock, extF, hnotE₁, ↓reduceIte,
          show (∃ a b, (G.induce V₂).IsLink e a b) from ⟨u, v, hl₂'⟩] at hr ⊢
        exact hr
    have hFext : ∀ e u v, F.graph.IsLink e u v → F.supportExtensor e ≠ 0 :=
      fun e u v hl => (hlinks e u v hl).1
    have hFE₁ : ∀ e u v, F.graph.IsLink e u v → e ∉ G.cutEdges V₁ →
        u ∈ V₁ ∧ v ∈ V₁ ∨ u ∉ V₁ ∧ v ∉ V₁ := by
      intro e u v hl hnotcut
      simp only [Graph.cutEdges, not_and, Set.mem_setOf_eq] at hnotcut
      by_cases hu₁ : u ∈ V₁
      · left; refine ⟨hu₁, ?_⟩
        by_contra hv₁
        exact (hnotcut hl.edge_mem) ⟨u, v, hl, hu₁, hv₁⟩
      · right; refine ⟨hu₁, ?_⟩
        by_contra hv₁
        exact (hnotcut hl.edge_mem) ⟨v, u, hl.symm, hv₁, hu₁⟩
    have hFcut : ∀ e ∈ G.cutEdges V₁, ∃ a b, F.graph.IsLink e a b ∧ a ∈ V₁ ∧ b ∉ V₁ := by
      intro e he
      simp only [Graph.cutEdges, Set.mem_setOf_eq] at he
      obtain ⟨_, a, b, hlab, ha, hb⟩ := he
      exact ⟨a, b, hlab, ha, hb⟩
    have hbrick := BodyHingeFramework.le_finrank_span_rigidityRows_of_cut F hcut_le hFext
      (fun e u v hl he => hFE₁ e u v hl he) hFcut
    rw [hF₁span, hF₂span] at hbrick
    have hrank₁ : (Module.finrank ℝ (Submodule.span ℝ F₁.rigidityRows) : ℤ)
        = screwDim 2 * ((V₁.ncard : ℤ) - 1) - k₁ := by
      rw [hVeq₁] at hF₁rank; rw [hF₁rank, hG₁.1]
    have hrank₂ : (Module.finrank ℝ (Submodule.span ℝ F₂.rigidityRows) : ℤ)
        = screwDim 2 * ((V₂.ncard : ℤ) - 1) - k₂ := by
      rw [hVeq₂] at hF₂rank; rw [hF₂rank, hG₂.1]
    have hFVne : V(F.graph).Nonempty := ⟨u₀, hV₁sub.subset hu₀⟩
    have hB2 := F.finrank_span_rigidityRows_add_deficiency_le hn hFVne hFext
    have hB2' : (Module.finrank ℝ (Submodule.span ℝ F.rigidityRows) : ℤ)
        ≤ screwDim 2 * ((V(G).ncard : ℤ) - 1) - k := by
      have := hB2; rw [hG.1] at this; linarith
    have hcardC1 : (G.cutEdges V₁).ncard = 1 :=
      Nat.le_antisymm hcut_le ((Set.ncard_pos (Set.toFinite _)).2 ⟨e_c, hec_mem⟩)
    have hlb : screwDim 2 * ((V(G).ncard : ℤ) - 1) - k ≤
        (Module.finrank ℝ (Submodule.span ℝ F.rigidityRows) : ℤ) := by
      have hbrickZ : (Module.finrank ℝ (Submodule.span ℝ F₁.rigidityRows) : ℤ) +
          (screwDim 2 - 1) * (G.cutEdges V₁).ncard +
          (Module.finrank ℝ (Submodule.span ℝ F₂.rigidityRows) : ℤ) ≤
          (Module.finrank ℝ (Submodule.span ℝ F.rigidityRows) : ℤ) := by exact_mod_cast hbrick
      rw [hrank₁, hrank₂] at hbrickZ
      rw [hn] at hk_eq
      rw [hcardC1] at hbrickZ hk_eq
      have hscrew : 1 ≤ screwDim 2 := by rw [← hn]; omega
      simp only [Nat.cast_sub hscrew, Nat.cast_one, mul_one] at hbrickZ hk_eq
      have hVcardZ : (V₁.ncard : ℤ) + V₂.ncard = V(G).ncard := by exact_mod_cast hVcard
      nlinarith
    have hrank_eq : (Module.finrank ℝ (Submodule.span ℝ F.rigidityRows) : ℤ)
        = screwDim 2 * ((V(G).ncard : ℤ) - 1) - k := le_antisymm hB2' hlb
    have hnorm_ne : ∀ v ∈ V(G), normal v ≠ 0 := by
      intro v hv
      simp only [normal]
      by_cases h₁ : v ∈ V₁
      · simp only [h₁, ↓reduceIte]
        exact hF₁ne v h₁
      · have h₂ : v ∈ V₂ := ⟨hv, h₁⟩
        simp only [h₁, ↓reduceIte, h₂]
        exact hF₂ne v h₂
    rw [← hG.1] at hrank_eq
    exact ⟨F, normal, rfl, hnorm_ne, hlinks, hrank_eq⟩

set_option maxHeartbeats 800000 in
-- The combined seed + per-side rank polynomials + |C|=0/1 case analysis exhausts the 200000 limit.
/-- **L4b-2 GP-conjunct producer: cut-edge case** (`lem:case-cut-edge-realization-gp`,
GP conjunct; Katoh–Tanigawa 2011 §6.1, Lemma 6.1, the `not-2EC` GP arm; Phase 22i).

Given a minimal `k`-dof simple graph `G` with `|V(G)| ≥ 3` that is not 2-edge-connected, the
generic-motive conjunct `HasGenericFullRankRealization 2 n G` holds.

**Proof sketch.** Cut decomposition (as L4a). Each side `G.induce Vᵢ` is simple (induced subgraph
of a simple graph), so the conditioned IH's `.1 hSimpleᵢ` supplies a side GP framework `QFᵢ`.
Seed `q₀ᵢ := fun p => QFᵢ.normal p.1 p.2`; GP transfers to `ofNormals (G.induce Vᵢ) G.endsOf q₀ᵢ`
(same normals, motion-space equality by swap-invariance → same finrank). W6e +
`exists_rankPolynomial_of_le_finrank_linking` → rational `Qᵢ_rank` transferring `Nᵢ = finrank QFᵢ`
rows. `exists_generalPosition_polynomial` → `Q_gp`. Fresh combined seed `q₀` from
`exists_injective_algebraicIndependent_real`; alg-indep seed is a non-root of every nonzero rational
polynomial, so `q₀` is a simultaneous non-root of `Q₁_rank · Q₂_rank · Q_gp`. Set
`QF := ofNormals G G.endsOf q₀`; global GP from `Q_gp`. Side rank bounds at `q₀` from the rank
transfer polynomials. Seed-free L4a brick + L1e arithmetic → combined lower bound. B2 → upper bound;
antisymmetry closes. Link-recording from `ofNormals_endsOf_recordsLinks`; alg-independence from
`halg`. -/
theorem case_cut_edge_realization_gp [DecidableEq β] [Finite α] [Finite β] {n : ℕ}
    (hD : 2 ≤ Graph.bodyBarDim n) (hn : Graph.bodyBarDim n = screwDim 2)
    {k : ℤ} (G : Graph α β) (hG : G.IsMinimalKDof n k) (_hV3 : 3 ≤ V(G).ncard)
    (hntec : ¬ G.TwoEdgeConnected) (hSimple : G.Simple)
    (hIH : ∀ (k' : ℤ) (G' : Graph α β), G'.IsMinimalKDof n k' → V(G').Nonempty →
      V(G').ncard < V(G).ncard →
      (G'.Simple → PanelHingeFramework.HasGenericFullRankRealization 2 n G') ∧
        HasPanelRealization 2 n G') :
    PanelHingeFramework.HasGenericFullRankRealization 2 n G := by
  classical
  -- ── Step 1: Cut decomposition ─────────────────────────────────────────────────────────
  obtain ⟨V₁, k₁, k₂, hV₁ne, hV₁sub, hV₂ne, hG₁, hG₂, hcut_le, hk_eq⟩ :=
    Graph.exists_cut_decomposition_of_not_twoEdgeConnected (by omega) hG hntec
  set V₂ := V(G) \ V₁
  -- Inhabited instance for G.endsOf (needs a vertex)
  haveI : Inhabited α := ⟨hV₁ne.choose⟩
  -- ── Step 2: Cardinality helpers ─────────────────────────────────────────────────────────
  have hV₁ncard : V(G.induce V₁).ncard < V(G).ncard :=
    Set.ncard_lt_ncard hV₁sub (Set.toFinite _)
  have hVcard : V₁.ncard + V₂.ncard = V(G).ncard := by
    have hunion : V₁ ∪ V₂ = V(G) := Set.union_diff_cancel hV₁sub.subset
    have hdisj : Disjoint V₁ V₂ := Set.disjoint_sdiff_right
    rw [← hunion, Set.ncard_union_eq hdisj (Set.toFinite V₁) (Set.toFinite V₂)]
  have hVeq₁ : V(G.induce V₁).ncard = V₁.ncard := rfl
  have hVeq₂ : V(G.induce V₂).ncard = V₂.ncard := rfl
  have hV₂ncard : V(G.induce V₂).ncard < V(G).ncard := by
    have hV₁pos : 0 < V₁.ncard := hV₁ne.ncard_pos
    omega
  -- ── Step 3: Side simplicity ─────────────────────────────────────────────────────────
  have hSimple₁ : (G.induce V₁).Simple :=
    hSimple.mono (G.induce_le hV₁sub.subset)
  have hSimple₂ : (G.induce V₂).Simple :=
    hSimple.mono (G.induce_le Set.diff_subset)
  -- ── Step 4: Side GP frameworks from IH ─────────────────────────────────────────────────
  obtain ⟨QF₁, hQF₁g, hQF₁gp, hQF₁rank, hQF₁rec, hQF₁alg⟩ :=
    (hIH k₁ (G.induce V₁) hG₁ hV₁ne hV₁ncard).1 hSimple₁
  obtain ⟨QF₂, hQF₂g, hQF₂gp, hQF₂rank, hQF₂rec, hQF₂alg⟩ :=
    (hIH k₂ (G.induce V₂) hG₂ hV₂ne hV₂ncard).1 hSimple₂
  -- ── Step 5: Side seeds ─────────────────────────────────────────────────────────────────
  -- Each side IH framework is literally `ofNormals (G.induce Vᵢ) QFᵢ.ends q₀ᵢ`
  -- at the seed `q₀ᵢ := fun p => QFᵢ.normal p.1 p.2`.
  set q₀₁ : α × Fin 4 → ℝ := fun p => QF₁.normal p.1 p.2
  set q₀₂ : α × Fin 4 → ℝ := fun p => QF₂.normal p.1 p.2
  -- ── Step 6: GP transfers to the G.endsOf selector ────────────────────────────────────────
  -- Same normals → same IsGeneralPosition on ofNormals (G.induce Vᵢ) G.endsOf q₀ᵢ.
  have hgp₁' : (PanelHingeFramework.ofNormals (G.induce V₁) G.endsOf q₀₁).IsGeneralPosition := by
    intro a b hab
    simp only [PanelHingeFramework.IsGeneralPosition, PanelHingeFramework.ofNormals_normal] at *
    exact hQF₁gp a b hab
  have hgp₂' : (PanelHingeFramework.ofNormals (G.induce V₂) G.endsOf q₀₂).IsGeneralPosition := by
    intro a b hab
    simp only [PanelHingeFramework.IsGeneralPosition, PanelHingeFramework.ofNormals_normal] at *
    exact hQF₂gp a b hab
  -- ── Step 7: Motion-space / finrank equality between QFᵢ.ends and G.endsOf at q₀ᵢ ─────────
  -- The swap-invariance of the motion space: G.endsOf ↔ QF₁.ends agree up to order on
  -- (G.induce V₁).
  have hswap₁ : ∀ e u v, (G.induce V₁).IsLink e u v →
      ((QF₁.ends e).1 = (G.endsOf e).1 ∧ (QF₁.ends e).2 = (G.endsOf e).2) ∨
      ((QF₁.ends e).1 = (G.endsOf e).2 ∧ (QF₁.ends e).2 = (G.endsOf e).1) :=
    PanelHingeFramework.recordsLinks_swap_endsOf
      (G.induce_le hV₁sub.subset) QF₁.ends hQF₁rec
  have hmot₁ :
      (PanelHingeFramework.ofNormals (G.induce V₁) G.endsOf q₀₁).toBodyHinge.infinitesimalMotions
      = (PanelHingeFramework.ofNormals (G.induce V₁) QF₁.ends q₀₁).toBodyHinge.infinitesimalMotions
      :=
    PanelHingeFramework.infinitesimalMotions_ofNormals_eq_of_ends_swap
      (G.induce V₁) G.endsOf QF₁.ends q₀₁ hswap₁
  -- The QF₁.ends version of ofNormals has the same infinitesimalMotions as QF₁.toBodyHinge,
  -- because they share the same graph and the same supportExtensor function on every link.
  have hmotQF₁ :
      (PanelHingeFramework.ofNormals (G.induce V₁) QF₁.ends q₀₁).toBodyHinge.infinitesimalMotions
      = QF₁.toBodyHinge.infinitesimalMotions :=
    BodyHingeFramework.infinitesimalMotions_eq_of_isLink_supportExtensor
      (PanelHingeFramework.ofNormals (G.induce V₁) QF₁.ends q₀₁).toBodyHinge
      QF₁.toBodyHinge
      (by simp [hQF₁g])
      (fun e u v _ => by
        simp only [PanelHingeFramework.toBodyHinge_supportExtensor,
          PanelHingeFramework.ofNormals_ends, PanelHingeFramework.ofNormals_normal, q₀₁])
  -- Same infinitesimalMotions → same finrank (span rigidityRows) via the complement identity.
  have hfinrank₁ : Module.finrank ℝ (Submodule.span ℝ
          (PanelHingeFramework.ofNormals (G.induce V₁) G.endsOf q₀₁).toBodyHinge.rigidityRows)
      = Module.finrank ℝ (Submodule.span ℝ QF₁.toBodyHinge.rigidityRows) := by
    have hcompl1 := BodyHingeFramework.finrank_span_rigidityRows_add_finrank_infinitesimalMotions
      (PanelHingeFramework.ofNormals (G.induce V₁) G.endsOf q₀₁).toBodyHinge
    have hcompl2 := BodyHingeFramework.finrank_span_rigidityRows_add_finrank_infinitesimalMotions
      QF₁.toBodyHinge
    rw [hmot₁, hmotQF₁] at hcompl1
    omega
  -- Analogously for side 2.
  have hswap₂ : ∀ e u v, (G.induce V₂).IsLink e u v →
      ((QF₂.ends e).1 = (G.endsOf e).1 ∧ (QF₂.ends e).2 = (G.endsOf e).2) ∨
      ((QF₂.ends e).1 = (G.endsOf e).2 ∧ (QF₂.ends e).2 = (G.endsOf e).1) :=
    PanelHingeFramework.recordsLinks_swap_endsOf
      (G.induce_le Set.diff_subset) QF₂.ends hQF₂rec
  have hmot₂ :
      (PanelHingeFramework.ofNormals (G.induce V₂) G.endsOf q₀₂).toBodyHinge.infinitesimalMotions
      = (PanelHingeFramework.ofNormals (G.induce V₂) QF₂.ends q₀₂).toBodyHinge.infinitesimalMotions
      :=
    PanelHingeFramework.infinitesimalMotions_ofNormals_eq_of_ends_swap
      (G.induce V₂) G.endsOf QF₂.ends q₀₂ hswap₂
  have hmotQF₂ :
      (PanelHingeFramework.ofNormals (G.induce V₂) QF₂.ends q₀₂).toBodyHinge.infinitesimalMotions
      = QF₂.toBodyHinge.infinitesimalMotions :=
    BodyHingeFramework.infinitesimalMotions_eq_of_isLink_supportExtensor
      (PanelHingeFramework.ofNormals (G.induce V₂) QF₂.ends q₀₂).toBodyHinge
      QF₂.toBodyHinge
      (by simp [hQF₂g])
      (fun e u v _ => by
        simp only [PanelHingeFramework.toBodyHinge_supportExtensor,
          PanelHingeFramework.ofNormals_ends, PanelHingeFramework.ofNormals_normal, q₀₂])
  have hfinrank₂ : Module.finrank ℝ (Submodule.span ℝ
          (PanelHingeFramework.ofNormals (G.induce V₂) G.endsOf q₀₂).toBodyHinge.rigidityRows)
      = Module.finrank ℝ (Submodule.span ℝ QF₂.toBodyHinge.rigidityRows) := by
    have hcompl1 := BodyHingeFramework.finrank_span_rigidityRows_add_finrank_infinitesimalMotions
      (PanelHingeFramework.ofNormals (G.induce V₂) G.endsOf q₀₂).toBodyHinge
    have hcompl2 := BodyHingeFramework.finrank_span_rigidityRows_add_finrank_infinitesimalMotions
      QF₂.toBodyHinge
    rw [hmot₂, hmotQF₂] at hcompl1
    omega
  -- ── Step 8: Build per-side rank polynomials ─────────────────────────────────────────
  -- Transversality witnesses at q₀ᵢ: nonzero extensor for (G.induce Vᵢ)-links at G.endsOf.
  have hne₁ : ∀ e, (G.induce V₁).IsLink e (G.endsOf e).1 (G.endsOf e).2 →
      (PanelHingeFramework.ofNormals (G.induce V₁) G.endsOf q₀₁).toBodyHinge.supportExtensor e
        ≠ 0 := by
    intro e he
    let P₁ := PanelHingeFramework.ofNormals (G.induce V₁) G.endsOf q₀₁
    apply P₁.supportExtensor_ne_zero_of_isGeneralPosition hgp₁'
    rw [PanelHingeFramework.ofNormals_ends]
    exact G.endsOf_fst_ne_snd (he.of_le (G.induce_le hV₁sub.subset)).edge_mem
  have hne₂ : ∀ e, (G.induce V₂).IsLink e (G.endsOf e).1 (G.endsOf e).2 →
      (PanelHingeFramework.ofNormals (G.induce V₂) G.endsOf q₀₂).toBodyHinge.supportExtensor e
        ≠ 0 := by
    intro e he
    let P₂ := PanelHingeFramework.ofNormals (G.induce V₂) G.endsOf q₀₂
    apply P₂.supportExtensor_ne_zero_of_isGeneralPosition hgp₂'
    rw [PanelHingeFramework.ofNormals_ends]
    exact G.endsOf_fst_ne_snd (he.of_le (G.induce_le Set.diff_subset)).edge_mem
  -- Rank bounds at q₀ᵢ from QFᵢ rank equality + finrank equality.
  have hN₁ : Module.finrank ℝ (Submodule.span ℝ QF₁.toBodyHinge.rigidityRows) ≤
      Module.finrank ℝ (Submodule.span ℝ
        (PanelHingeFramework.ofNormals (G.induce V₁) G.endsOf q₀₁).toBodyHinge.rigidityRows) :=
    hfinrank₁.symm ▸ le_refl _
  have hN₂ : Module.finrank ℝ (Submodule.span ℝ QF₂.toBodyHinge.rigidityRows) ≤
      Module.finrank ℝ (Submodule.span ℝ
        (PanelHingeFramework.ofNormals (G.induce V₂) G.endsOf q₀₂).toBodyHinge.rigidityRows) :=
    hfinrank₂.symm ▸ le_refl _
  -- hends helper: (G.induce Vᵢ)-links have (G.endsOf e) endpoints in G.induce Vᵢ.
  have hends₁ : ∀ e u v, (G.induce V₁).IsLink e u v →
      (G.induce V₁).IsLink e (G.endsOf e).1 (G.endsOf e).2 := by
    intro e u v he
    have hGlink : G.IsLink e u v := he.1
    rcases G.endsOf_eq_or_swap hGlink with h | h
    · rw [h]; exact (Graph.induce_isLink G V₁ e u v).mpr ⟨hGlink, he.2.1, he.2.2⟩
    · rw [h]; exact (Graph.induce_isLink G V₁ e v u).mpr ⟨hGlink.symm, he.2.2, he.2.1⟩
  have hends₂ : ∀ e u v, (G.induce V₂).IsLink e u v →
      (G.induce V₂).IsLink e (G.endsOf e).1 (G.endsOf e).2 := by
    intro e u v he
    have hGlink : G.IsLink e u v := he.1
    rcases G.endsOf_eq_or_swap hGlink with h | h
    · rw [h]; exact (Graph.induce_isLink G V₂ e u v).mpr ⟨hGlink, he.2.1, he.2.2⟩
    · rw [h]; exact (Graph.induce_isLink G V₂ e v u).mpr ⟨hGlink.symm, he.2.2, he.2.1⟩
  -- Per-side rank polynomials.
  obtain ⟨Q₁_rank, hQ₁ne, hQ₁rat, hQ₁trans⟩ :=
    PanelHingeFramework.exists_rankPolynomial_of_le_finrank_linking
      (G.induce V₁) G.endsOf hends₁ hne₁ hN₁
  obtain ⟨Q₂_rank, hQ₂ne, hQ₂rat, hQ₂trans⟩ :=
    PanelHingeFramework.exists_rankPolynomial_of_le_finrank_linking
      (G.induce V₂) G.endsOf hends₂ hne₂ hN₂
  -- ── Step 9: GP polynomial ──────────────────────────────────────────────────────────────────
  obtain ⟨Q_gp, hQgpne_witness, hQgprat, hQgp_pos⟩ :=
    PanelHingeFramework.exists_generalPosition_polynomial (k := 2) G G.endsOf
  -- ── Step 10: Fresh combined seed (non-root of Q₁_rank · Q₂_rank · Q_gp) ─────────────────────
  have hQ₁rane : Q₁_rank ≠ 0 := fun h => hQ₁ne (by rw [h, map_zero])
  have hQ₂rane : Q₂_rank ≠ 0 := fun h => hQ₂ne (by rw [h, map_zero])
  have hQgpne : Q_gp ≠ 0 := by
    obtain ⟨f, hf⟩ := Countable.exists_injective_nat α
    intro h
    exact hQgpne_witness (fun a => (f a : ℝ)) (fun a b hab => hf (Nat.cast_injective hab))
      (by rw [h, map_zero])
  obtain ⟨q₀, _, halg⟩ := exists_injective_algebraicIndependent_real (α × Fin (2 + 2))
  have hq₀₁ : MvPolynomial.eval q₀ Q₁_rank ≠ 0 :=
    MvPolynomial.eval_ne_zero_of_coeffs_subset_range_of_algebraicIndependent halg hQ₁rat hQ₁rane
  have hq₀₂ : MvPolynomial.eval q₀ Q₂_rank ≠ 0 :=
    MvPolynomial.eval_ne_zero_of_coeffs_subset_range_of_algebraicIndependent halg hQ₂rat hQ₂rane
  have hq₀gp : MvPolynomial.eval q₀ Q_gp ≠ 0 :=
    MvPolynomial.eval_ne_zero_of_coeffs_subset_range_of_algebraicIndependent halg hQgprat hQgpne
  -- ── Step 11: The combined framework at q₀ ─────────────────────────────────────────────────
  -- QF = ofNormals G G.endsOf q₀ : PanelHingeFramework 2 α β
  -- Global GP from Q_gp non-root.
  have hQFgp : (PanelHingeFramework.ofNormals G G.endsOf q₀).IsGeneralPosition :=
    hQgp_pos q₀ hq₀gp
  -- For any G-link, the combined framework's extensor is nonzero (GP + looplessness).
  have hQFext : ∀ e u v, G.IsLink e u v →
      (PanelHingeFramework.ofNormals G G.endsOf q₀).toBodyHinge.supportExtensor e ≠ 0 := by
    intro e u v he
    apply (PanelHingeFramework.ofNormals G G.endsOf q₀).supportExtensor_ne_zero_of_isGeneralPosition
      hQFgp
    rw [PanelHingeFramework.ofNormals_ends]
    exact G.endsOf_fst_ne_snd he.edge_mem
  -- ── Step 12: Side span equalities ─────────────────────────────────────────────────────────
  -- The rigidity rows of ⟨G.induce Vᵢ, (ofNormals G G.endsOf q₀).toBodyHinge.supportExtensor⟩
  -- equal those of ofNormals (G.induce Vᵢ) G.endsOf q₀, since both use the same extensor function
  -- panelSupportExtensor (q₀ (G.endsOf e).1) (q₀ (G.endsOf e).2) on edges in G.induce Vᵢ.
  have hF₁span : Submodule.span ℝ
        (⟨G.induce V₁, (PanelHingeFramework.ofNormals G G.endsOf q₀).toBodyHinge.supportExtensor⟩
          : BodyHingeFramework 2 α β).rigidityRows
      = Submodule.span ℝ
        (PanelHingeFramework.ofNormals (G.induce V₁) G.endsOf q₀).toBodyHinge.rigidityRows := by
    congr 1
  have hF₂span : Submodule.span ℝ
        (⟨G.induce V₂, (PanelHingeFramework.ofNormals G G.endsOf q₀).toBodyHinge.supportExtensor⟩
          : BodyHingeFramework 2 α β).rigidityRows
      = Submodule.span ℝ
        (PanelHingeFramework.ofNormals (G.induce V₂) G.endsOf q₀).toBodyHinge.rigidityRows := by
    congr 1
  -- ── Step 13: Side rank lower bounds at q₀ ─────────────────────────────────────────────────
  -- From the rank transfer polynomials evaluated at q₀.
  have hrank₁_bound : Module.finrank ℝ (Submodule.span ℝ QF₁.toBodyHinge.rigidityRows) ≤
      Module.finrank ℝ
        (Submodule.span ℝ
          (PanelHingeFramework.ofNormals (G.induce V₁) G.endsOf q₀).toBodyHinge.rigidityRows) :=
    hQ₁trans q₀ hq₀₁
  have hrank₂_bound : Module.finrank ℝ (Submodule.span ℝ QF₂.toBodyHinge.rigidityRows) ≤
      Module.finrank ℝ
        (Submodule.span ℝ
          (PanelHingeFramework.ofNormals (G.induce V₂) G.endsOf q₀).toBodyHinge.rigidityRows) :=
    hQ₂trans q₀ hq₀₂
  -- ── Step 14: Apply the L4a brick ─────────────────────────────────────────────────────────
  -- F := (ofNormals G G.endsOf q₀).toBodyHinge
  set F := (PanelHingeFramework.ofNormals G G.endsOf q₀).toBodyHinge
  have hFgraph : F.graph = G := by simp [F, PanelHingeFramework.ofNormals_graph]
  -- The FE₁ and Fcut hypotheses for the brick.
  have hFE₁ : ∀ e u v, F.graph.IsLink e u v → e ∉ G.cutEdges V₁ →
      u ∈ V₁ ∧ v ∈ V₁ ∨ u ∉ V₁ ∧ v ∉ V₁ := by
    intro e u v hl hnotcut
    simp only [Graph.cutEdges, not_and, Set.mem_setOf_eq] at hnotcut
    rw [hFgraph] at hl
    by_cases hu₁ : u ∈ V₁
    · left; refine ⟨hu₁, ?_⟩
      by_contra hv₁
      exact (hnotcut hl.edge_mem) ⟨u, v, hl, hu₁, hv₁⟩
    · right; refine ⟨hu₁, ?_⟩
      by_contra hv₁
      exact (hnotcut hl.edge_mem) ⟨v, u, hl.symm, hv₁, hu₁⟩
  have hFext' : ∀ e u v, F.graph.IsLink e u v → F.supportExtensor e ≠ 0 := by
    intro e u v hl
    rw [hFgraph] at hl
    exact hQFext e u v hl
  rcases Set.eq_empty_or_nonempty (G.cutEdges V₁) with hC0 | ⟨e_c, he_c⟩
  · -- ── Case |C| = 0 ─────────────────────────────────────────────────────────────────────
    have hFcut : ∀ e ∈ G.cutEdges V₁, ∃ a b, F.graph.IsLink e a b ∧ a ∈ V₁ ∧ b ∉ V₁ := by
      intro e he; simp [hC0] at he
    have hbrick := BodyHingeFramework.le_finrank_span_rigidityRows_of_cut F hcut_le hFext'
      (fun e u v hl he => hFE₁ e u v hl he) hFcut
    rw [hFgraph] at hbrick
    rw [hF₁span, hF₂span] at hbrick
    -- Rank equalities from the side IH.
    have hrank₁eq : (Module.finrank ℝ (Submodule.span ℝ QF₁.toBodyHinge.rigidityRows) : ℤ)
        = screwDim 2 * ((V₁.ncard : ℤ) - 1) - k₁ := by
      have := hQF₁rank; rw [hVeq₁, hG₁.1] at this; exact this
    have hrank₂eq : (Module.finrank ℝ (Submodule.span ℝ QF₂.toBodyHinge.rigidityRows) : ℤ)
        = screwDim 2 * ((V₂.ncard : ℤ) - 1) - k₂ := by
      have := hQF₂rank; rw [hVeq₂, hG₂.1] at this; exact this
    -- Combined lower bound from the brick + side ranks.
    have hFVne : V(F.graph).Nonempty := by
      rw [hFgraph]; exact ⟨hV₁ne.choose, hV₁sub.subset hV₁ne.choose_spec⟩
    have hB2 := F.finrank_span_rigidityRows_add_deficiency_le hn hFVne hFext'
    have hB2' : (Module.finrank ℝ (Submodule.span ℝ F.rigidityRows) : ℤ)
        ≤ screwDim 2 * ((V(G).ncard : ℤ) - 1) - k := by
      rw [hFgraph] at hB2
      have := hB2; rw [hG.1] at this; linarith
    have hlb : screwDim 2 * ((V(G).ncard : ℤ) - 1) - k ≤
        (Module.finrank ℝ (Submodule.span ℝ F.rigidityRows) : ℤ) := by
      let R₁ := Module.finrank ℝ (Submodule.span ℝ
          (PanelHingeFramework.ofNormals (G.induce V₁) G.endsOf q₀).toBodyHinge.rigidityRows)
      let R₂ := Module.finrank ℝ (Submodule.span ℝ
          (PanelHingeFramework.ofNormals (G.induce V₂) G.endsOf q₀).toBodyHinge.rigidityRows)
      have hbrickZ : (R₁ : ℤ) + (screwDim 2 - 1) * (G.cutEdges V₁).ncard + (R₂ : ℤ) ≤
          (Module.finrank ℝ (Submodule.span ℝ F.rigidityRows) : ℤ) := by exact_mod_cast hbrick
      have h₁ : (Module.finrank ℝ (Submodule.span ℝ QF₁.toBodyHinge.rigidityRows) : ℤ) ≤
          (R₁ : ℤ) := by exact_mod_cast hrank₁_bound
      have h₂ : (Module.finrank ℝ (Submodule.span ℝ QF₂.toBodyHinge.rigidityRows) : ℤ) ≤
          (R₂ : ℤ) := by exact_mod_cast hrank₂_bound
      rw [hn] at hk_eq
      simp only [hC0, Set.ncard_empty] at hbrickZ hk_eq
      have hscrew : 1 ≤ screwDim 2 := by rw [← hn]; omega
      push_cast [Nat.sub_add_cancel hscrew] at hbrickZ hk_eq h₁ h₂ ⊢
      simp only [mul_zero, add_zero, sub_zero] at hbrickZ hk_eq
      have hVcardZ : (V₁.ncard : ℤ) + V₂.ncard = V(G).ncard := by exact_mod_cast hVcard
      nlinarith [hrank₁eq, hrank₂eq]
    have hrank_eq : (Module.finrank ℝ (Submodule.span ℝ F.rigidityRows) : ℤ)
        = screwDim 2 * ((V(G).ncard : ℤ) - 1) - k := le_antisymm hB2' hlb
    -- Conclude: ofNormals G G.endsOf q₀ is the GP realization.
    rw [← hG.1] at hrank_eq
    exact ⟨PanelHingeFramework.ofNormals G G.endsOf q₀, rfl, hQFgp, hrank_eq,
      PanelHingeFramework.ofNormals_endsOf_recordsLinks G q₀,
      by simpa only [PanelHingeFramework.ofNormals_normal] using halg⟩
  · -- ── Case |C| = 1 ─────────────────────────────────────────────────────────────────────
    -- he_c : e_c ∈ G.cutEdges V₁ directly (from Set.eq_empty_or_nonempty)
    have hFcut : ∀ e ∈ G.cutEdges V₁, ∃ a b, F.graph.IsLink e a b ∧ a ∈ V₁ ∧ b ∉ V₁ := by
      intro e he; simp only [Graph.cutEdges, Set.mem_setOf_eq] at he
      obtain ⟨_, a, b, hlab, ha, hb⟩ := he
      exact ⟨a, b, by simp [F, hlab], ha, hb⟩
    have hbrick := BodyHingeFramework.le_finrank_span_rigidityRows_of_cut F hcut_le hFext'
      (fun e u v hl he => hFE₁ e u v hl he) hFcut
    rw [hFgraph] at hbrick
    rw [hF₁span, hF₂span] at hbrick
    have hrank₁eq : (Module.finrank ℝ (Submodule.span ℝ QF₁.toBodyHinge.rigidityRows) : ℤ)
        = screwDim 2 * ((V₁.ncard : ℤ) - 1) - k₁ := by
      have := hQF₁rank; rw [hVeq₁, hG₁.1] at this; exact this
    have hrank₂eq : (Module.finrank ℝ (Submodule.span ℝ QF₂.toBodyHinge.rigidityRows) : ℤ)
        = screwDim 2 * ((V₂.ncard : ℤ) - 1) - k₂ := by
      have := hQF₂rank; rw [hVeq₂, hG₂.1] at this; exact this
    have hcardC1 : (G.cutEdges V₁).ncard = 1 :=
      Nat.le_antisymm hcut_le ((Set.ncard_pos (Set.toFinite _)).2 ⟨e_c, he_c⟩)
    have hFVne : V(F.graph).Nonempty := by
      rw [hFgraph]; exact ⟨hV₁ne.choose, hV₁sub.subset hV₁ne.choose_spec⟩
    have hB2 := F.finrank_span_rigidityRows_add_deficiency_le hn hFVne hFext'
    have hB2' : (Module.finrank ℝ (Submodule.span ℝ F.rigidityRows) : ℤ)
        ≤ screwDim 2 * ((V(G).ncard : ℤ) - 1) - k := by
      rw [hFgraph] at hB2
      have := hB2; rw [hG.1] at this; linarith
    have hlb : screwDim 2 * ((V(G).ncard : ℤ) - 1) - k ≤
        (Module.finrank ℝ (Submodule.span ℝ F.rigidityRows) : ℤ) := by
      let R₁ := Module.finrank ℝ (Submodule.span ℝ
          (PanelHingeFramework.ofNormals (G.induce V₁) G.endsOf q₀).toBodyHinge.rigidityRows)
      let R₂ := Module.finrank ℝ (Submodule.span ℝ
          (PanelHingeFramework.ofNormals (G.induce V₂) G.endsOf q₀).toBodyHinge.rigidityRows)
      have hbrickZ : (R₁ : ℤ) + (screwDim 2 - 1) * (G.cutEdges V₁).ncard + (R₂ : ℤ) ≤
          (Module.finrank ℝ (Submodule.span ℝ F.rigidityRows) : ℤ) := by exact_mod_cast hbrick
      have h₁ : (Module.finrank ℝ (Submodule.span ℝ QF₁.toBodyHinge.rigidityRows) : ℤ) ≤
          (R₁ : ℤ) := by exact_mod_cast hrank₁_bound
      have h₂ : (Module.finrank ℝ (Submodule.span ℝ QF₂.toBodyHinge.rigidityRows) : ℤ) ≤
          (R₂ : ℤ) := by exact_mod_cast hrank₂_bound
      rw [hn] at hk_eq
      rw [hcardC1] at hbrickZ hk_eq
      have hscrew : 1 ≤ screwDim 2 := by rw [← hn]; omega
      simp only [Nat.cast_sub hscrew, Nat.cast_one, mul_one] at hbrickZ hk_eq
      have hVcardZ : (V₁.ncard : ℤ) + V₂.ncard = V(G).ncard := by exact_mod_cast hVcard
      nlinarith [hrank₁eq, hrank₂eq]
    have hrank_eq : (Module.finrank ℝ (Submodule.span ℝ F.rigidityRows) : ℤ)
        = screwDim 2 * ((V(G).ncard : ℤ) - 1) - k := le_antisymm hB2' hlb
    rw [← hG.1] at hrank_eq
    exact ⟨PanelHingeFramework.ofNormals G G.endsOf q₀, rfl, hQFgp, hrank_eq,
      PanelHingeFramework.ofNormals_endsOf_recordsLinks G q₀,
      by simpa only [PanelHingeFramework.ofNormals_normal] using halg⟩

set_option maxHeartbeats 800000 in
-- The splice-brick assembly (Step 9) is elaboration-heavy; 800000 suffices in practice.
/-- **L5a-ii producer: non-simple Case I arm** (`lem:case-I-realization-nonsimple`;
KT Lemma 6.2, the parallel-edge contraction arm; Phase 22i).

Given a minimal `k`-dof graph `G` with `|V(G)| ≥ 3` that is **not simple** (has a parallel pair
`e, f` joining some vertices `a, b`), the genuine-hinge panel realization motive
`HasPanelRealization 2 n G` holds.

**Proof sketch.** `¬G.Simple` + looplessness (from `IsMinimalKDof`) gives vertices `a, b` and
parallel edges `e, f` with `G.IsLink e a b` and `G.IsLink f a b` and `e ≠ f`. Build
`H' := G[{a, b}] ↾ {e, f}`, a proper rigid subgraph (`isKDof_zero_of_parallel_pair`, `{a,b}` has
ncard 2, and `|V(G)| ≥ 3`). Contract: `G.rigidContract H' a` is minimal `k`-dof
(`rigidContract_isMinimalKDof`) with `|V(G.rigidContract H' a)| < |V(G)|`; IH gives `Fc_fw`.
Build the H'-leg framework `FH` with coincident panels at `a` and `b` (degenerate placement
`Fc_normal ∘ collapseTo a V(H')`, so both panels equal `Fc_normal a`) and LI extensors `Ce, Cf`
(`exists_linearIndependent_extensor_pair_perp`). Rigidity of `FH` on `{a,b}` (`theorem_55_base`)
+ B1 gives `finrank FH = D`. Assemble `F` from `FH` for H'-edges, `Fc_fw` for surviving edges.
Four splice-brick hypotheses: `hFH_ker` from `hingeRow_comp_extProj_eq_zero`; `hFc_surv_le` from
`hingeRow_collapseTo_comp_extProj_eq`; `hInj` from
`finrank_span_rigidityRows_map_extProj_dualMap_of_inter_eq_singleton` +
`rigidContract_vertexSet_inter_eq_singleton`. Brick gives `D + finrank Fc ≤ finrank F`; B2 gives
`finrank F ≤ D(|V|−1) − k`; arithmetic (`D + (D(|V|−2)−k) = D(|V|−1)−k`) closes M2. -/
theorem case_I_realization_nonsimple [DecidableEq β] [Finite α] [Finite β] {n : ℕ}
    (hD : 2 ≤ Graph.bodyBarDim n) (hn : Graph.bodyBarDim n = screwDim 2)
    {k : ℤ} (G : Graph α β) (hG : G.IsMinimalKDof n k) (_hV3 : 3 ≤ V(G).ncard)
    (hnsimple : ¬ G.Simple)
    (hIH : ∀ (k' : ℤ) (G' : Graph α β), G'.IsMinimalKDof n k' → V(G').Nonempty →
      V(G').ncard < V(G).ncard → HasPanelRealization 2 n G') :
    HasPanelRealization 2 n G := by
  classical
  haveI : NeZero (Graph.bodyHingeMult n) := ⟨by rw [Graph.bodyHingeMult]; omega⟩
  -- ── Step 1: Extract looplessness + parallel pair ─────────────────────────────────────────
  haveI hloop : G.Loopless := Graph.loopless_of_isMinimalKDof hG
  -- ¬G.Simple + G.Loopless gives a parallel pair.
  have hpairs : ∃ e_edge f_edge : β, ∃ a b : α,
      G.IsLink e_edge a b ∧ G.IsLink f_edge a b ∧ e_edge ≠ f_edge := by
    simp only [Graph.simple_iff, not_and_or] at hnsimple
    rcases hnsimple with hloopFalse | hnotAll
    · exact absurd hloop hloopFalse
    · push Not at hnotAll
      obtain ⟨e, f, x, y, hlex, hlfy, hef⟩ := hnotAll
      exact ⟨e, f, x, y, hlex, hlfy, hef⟩
  obtain ⟨e_edge, f_edge, a, b, hle, hlf, hef⟩ := hpairs
  have hab : a ≠ b := hle.ne
  -- ── Step 2: Build H' = G[{a,b}] ↾ {e_edge, f_edge} ──────────────────────────────────────
  set H' : Graph α β := G.induce {a, b} ↾ {e_edge, f_edge} with hH'_def
  have hVH' : V(H') = {a, b} := by
    simp only [hH'_def, Graph.vertexSet_restrict, Graph.vertexSet_induce]
  have hH'a : a ∈ V(H') := by rw [hVH']; exact Set.mem_insert a _
  have hH'b : b ∈ V(H') := by rw [hVH']; simp
  have hH'le : H'.IsLink e_edge a b := by
    simp only [hH'_def, Graph.restrict_isLink, Graph.induce_isLink]
    exact ⟨Set.mem_insert _ _, hle, Set.mem_insert a _, by simp⟩
  have hH'lf : H'.IsLink f_edge a b := by
    simp only [hH'_def, Graph.restrict_isLink, Graph.induce_isLink]
    exact ⟨by simp, hlf, Set.mem_insert a _, by simp⟩
  -- e_edge, f_edge ∈ E(G[{a,b}]) (used in hEH' below).
  have he_in_ind : e_edge ∈ E(G.induce {a, b}) :=
    ((Graph.induce_isLink G {a, b} e_edge a b).mpr
      ⟨hle, Set.mem_insert a _, by simp⟩).edge_mem
  have hf_in_ind : f_edge ∈ E(G.induce {a, b}) :=
    ((Graph.induce_isLink G {a, b} f_edge a b).mpr
      ⟨hlf, Set.mem_insert a _, by simp⟩).edge_mem
  have hEH' : E(H') = {e_edge, f_edge} := by
    rw [hH'_def, Graph.edgeSet_restrict]
    ext e; simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · intro ⟨_, he⟩; exact he
    · rintro (rfl | rfl)
      · exact ⟨he_in_ind, Or.inl rfl⟩
      · exact ⟨hf_in_ind, Or.inr rfl⟩
  have hH'leG : H' ≤ G := by
    refine ⟨?_, ?_⟩
    · rw [hVH']; intro v hv; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
      rcases hv with rfl | rfl
      · exact hle.left_mem
      · exact hle.right_mem
    · intro e u v hlink
      have hrl := (Graph.restrict_isLink _ _ e u v).mp (hH'_def ▸ hlink)
      exact ((Graph.induce_isLink G {a, b} e u v).mp hrl.2).1
  -- ── Step 3: H' is a proper rigid subgraph ────────────────────────────────────────────────
  have hVH'ncard : V(H').ncard = 2 := by rw [hVH', Set.ncard_pair hab]
  have hH'rigid : H'.IsKDof n 0 :=
    Graph.isKDof_zero_of_parallel_pair hD hab hH'le hH'lf hef hVH' hEH'
  have hHsub : V(H') ⊆ V(G) := hH'leG.vertexSet_mono
  have hH'proper : H'.IsProperRigidSubgraph G n := by
    refine ⟨⟨hH'leG, hH'rigid⟩, by rw [hVH'ncard], ?_⟩
    refine ⟨hHsub, fun hrev => ?_⟩
    have : V(G).ncard ≤ V(H').ncard := Set.ncard_le_ncard hrev (Set.toFinite _)
    rw [hVH'ncard] at this; omega
  -- ── Step 4: IH on the contraction ────────────────────────────────────────────────────────
  have hKlt : V(G.rigidContract H' a).ncard < V(G).ncard :=
    Graph.rigidContract_vertexSet_ncard_lt hHsub (by rw [hVH'ncard])
  have hKmin : (G.rigidContract H' a).IsMinimalKDof n k :=
    Graph.rigidContract_isMinimalKDof hG hH'proper hH'a
  have hKne : V(G.rigidContract H' a).Nonempty := by
    apply (Set.ncard_pos (Set.toFinite _)).mp
    rw [Graph.rigidContract_vertexSet_ncard hH'a hHsub, hVH'ncard]; omega
  obtain ⟨Fc_fw, Fc_normal, hFcg, hFcne, hFcext, hFcrank⟩ :=
    hIH k (G.rigidContract H' a) hKmin hKne hKlt
  have hKcard : V(G.rigidContract H' a).ncard = V(G).ncard - 1 := by
    rw [Graph.rigidContract_vertexSet_ncard hH'a hHsub, hVH'ncard]; omega
  -- ── Step 5: Degenerate normals ───────────────────────────────────────────────────────────
  -- Both a and b get Fc_normal a
  -- (= Fc_normal (collapseTo a V(H') a) = Fc_normal (collapseTo a V(H') b)).
  set normal : α → Fin 4 → ℝ := fun v => Fc_normal (Graph.collapseTo a V(H') v)
  have hnorm_ne : ∀ v ∈ V(G), normal v ≠ 0 := by
    intro v hv; simp only [normal]
    apply hFcne
    simp only [Graph.vertexSet_rigidContract]
    exact ⟨v, hv, rfl⟩
  -- ── Step 6: LI extensors Ce, Cf in (normal a)^⊥ ────────────────────────────────────────
  obtain ⟨p, q, hp_perp, hq_perp, hpq_li⟩ :=
    exists_linearIndependent_extensor_pair_perp (normal a)
  set Ce : ScrewSpace 2 := ⟨extensor p, extensor_mem_exteriorPower _⟩
  set Cf : ScrewSpace 2 := ⟨extensor q, extensor_mem_exteriorPower _⟩
  have hCe_ne : Ce ≠ 0 := by simpa using hpq_li.ne_zero 0
  have hCf_ne : Cf ≠ 0 := by simpa using hpq_li.ne_zero 1
  have hCe_perp : ExtensorInPanel Ce (normal a) := ⟨p, rfl, hp_perp⟩
  have hCf_perp : ExtensorInPanel Cf (normal a) := ⟨q, rfl, hq_perp⟩
  -- normal b = normal a (both collapse to a under collapseTo a V(H')).
  have hn_b_eq : normal b = normal a := by
    simp only [normal, Graph.collapseTo, hH'b, hH'a, ↓reduceIte]
  -- ── Step 7: Assemble F and FH ─────────────────────────────────────────────────────────────
  set extF : β → ScrewSpace 2 := fun e =>
    if e = e_edge then Ce else if e = f_edge then Cf else Fc_fw.supportExtensor e
  set F : BodyHingeFramework 2 α β := { graph := G, supportExtensor := extF }
  set FH : BodyHingeFramework 2 α β := { graph := H', supportExtensor := extF }
  have hFg : F.graph = G := rfl
  have hFHg : FH.graph = H' := rfl
  have hFe : extF e_edge = Ce := by simp [extF]
  have hFf : extF f_edge = Cf := by simp [extF, hef.symm]
  -- e_edge ≠ f_edge and the ite values.
  have hef_ne : e_edge ≠ f_edge := hef
  -- For surviving edges e' ∉ {e_edge, f_edge}: extF e' = Fc_fw.supportExtensor e'.
  have hextF_surv : ∀ e' : β, e' ≠ e_edge → e' ≠ f_edge →
      extF e' = Fc_fw.supportExtensor e' := by
    intro e' hne1 hne2; simp [extF, hne1, hne2]
  -- ── Step 8: finrank FH = D via theorem_55_base + B1 ──────────────────────────────────────
  have hFH_li : LinearIndependent ℝ ![FH.supportExtensor e_edge, FH.supportExtensor f_edge] := by
    change LinearIndependent ℝ ![extF e_edge, extF f_edge]
    rw [hFe, hFf]; exact hpq_li
  have hFHne : FH.graph.vertexSet.Nonempty := by
    rw [hFHg, hVH']; exact ⟨a, Set.mem_insert a _⟩
  have hFH_rig : FH.IsInfinitesimallyRigidOn {a, b} :=
    FH.theorem_55_base hab hFH_li (hFHg ▸ hH'le) (hFHg ▸ hH'lf)
  have hFH_rigV : FH.IsInfinitesimallyRigidOn FH.graph.vertexSet := by
    rw [hFHg, hVH']; exact hFH_rig
  have hFH_finrank_nat : Module.finrank ℝ (Submodule.span ℝ FH.rigidityRows)
      = screwDim 2 * (V(H').ncard - 1) :=
    (FH.isInfinitesimallyRigidOn_vertexSet_iff_finrank_span_rigidityRows hFHne).mp
      (hFHg ▸ hFH_rigV)
  have hFH_finrank : (Module.finrank ℝ (Submodule.span ℝ FH.rigidityRows) : ℤ) = screwDim 2 := by
    rw [hFH_finrank_nat, hVH'ncard]; push_cast; ring
  -- ── Step 9: Splice brick hypotheses ─────────────────────────────────────────────────────
  set t := V(H') with ht_def
  set Dmap := (extProj (k := 2) t).dualMap
  -- (i) hFH_le: FH rows ≤ F rows (same extensor; H' ≤ G).
  have hFH_le : Submodule.span ℝ FH.rigidityRows ≤ Submodule.span ℝ F.rigidityRows := by
    apply Submodule.span_mono
    intro φ hφ
    simp only [BodyHingeFramework.rigidityRows, Set.mem_setOf_eq] at hφ ⊢
    obtain ⟨e, u, v, hlink, r, hr, rfl⟩ := hφ
    exact ⟨e, u, v, hH'leG.isLink_mono hlink, r,
      by simpa [BodyHingeFramework.hingeRowBlock, FH, F] using hr, rfl⟩
  -- (ii) hFH_ker: FH rows ≤ ker Dmap (H'-link endpoints are in t = V(H')).
  have hFH_ker : Submodule.span ℝ FH.rigidityRows ≤ LinearMap.ker Dmap := by
    apply Submodule.span_le.mpr
    intro φ hφ
    simp only [BodyHingeFramework.rigidityRows, Set.mem_setOf_eq] at hφ
    obtain ⟨e, u, v, hlink, r, hr, rfl⟩ := hφ
    have hu : u ∈ t := by simp only [ht_def]; exact hFHg ▸ hlink.left_mem
    have hv : v ∈ t := by simp only [ht_def]; exact hFHg ▸ hlink.right_mem
    change Dmap (BodyHingeFramework.hingeRow u v r) = 0
    simp only [Dmap, LinearMap.dualMap_apply']
    exact hingeRow_comp_extProj_eq_zero hu hv r
  -- (iii) hInj: finrank Fc_fw = finrank (Fc_fw span).map Dmap.
  have hFcg_inter : Fc_fw.graph.vertexSet ∩ t = {a} := by
    rw [ht_def, hFcg]
    exact Graph.rigidContract_vertexSet_inter_eq_singleton G H' hH'a hHsub
  have hInj : Module.finrank ℝ ↥(Submodule.span ℝ Fc_fw.rigidityRows) =
      Module.finrank ℝ ↥((Submodule.span ℝ Fc_fw.rigidityRows).map Dmap) :=
    Fc_fw.finrank_span_rigidityRows_map_extProj_dualMap_of_inter_eq_singleton hFcg_inter
  -- (iv) hFc_surv_le: (span Fc rows).map Dmap ≤ (span F rows).map Dmap.
  -- Strategy: for each generator hingeRow u' v' r' of Fc rows (where u' = collapseTo a t u,
  -- v' = collapseTo a t v for a G-surviving-edge link G.IsLink e' u v),
  -- Dmap(hingeRow u' v' r') = Dmap(hingeRow u v r') by hingeRow_collapseTo_comp_extProj_eq,
  -- and hingeRow u v r' ∈ F.rigidityRows (since extF e' = Fc_fw.supportExtensor e' for e' ∉ E(H')).
  have hFc_surv_le : (Submodule.span ℝ Fc_fw.rigidityRows).map Dmap ≤
      (Submodule.span ℝ F.rigidityRows).map Dmap := by
    rw [Submodule.map_span, Submodule.map_span]
    apply Submodule.span_mono
    intro ψ hψ
    simp only [Set.mem_image, BodyHingeFramework.rigidityRows, Set.mem_setOf_eq] at hψ
    obtain ⟨φ, ⟨e', u', v', hlink', r', hr', rfl⟩, rfl⟩ := hψ
    -- Unpack the rigidContract link: hlink' : Fc_fw.graph.IsLink e' u' v'.
    rw [hFcg, Graph.rigidContract, Graph.map_isLink] at hlink'
    obtain ⟨u, v, hGdel, rfl, rfl⟩ := hlink'
    rw [Graph.deleteEdges_isLink] at hGdel
    obtain ⟨hGlink, hnotEH'⟩ := hGdel
    rw [hEH'] at hnotEH'
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hnotEH'
    obtain ⟨hne1, hne2⟩ := hnotEH'
    have hextEq : extF e' = Fc_fw.supportExtensor e' := hextF_surv e' hne1 hne2
    have hr'F : r' ∈ (F : BodyHingeFramework 2 α β).hingeRowBlock e' := by
      simpa [BodyHingeFramework.hingeRowBlock, F, hextEq] using hr'
    have ha_t : a ∈ t := hH'a
    have hrow_eq : Dmap (BodyHingeFramework.hingeRow (Graph.collapseTo a t u)
          (Graph.collapseTo a t v) r') =
        Dmap (BodyHingeFramework.hingeRow u v r') := by
      simp only [Dmap, LinearMap.dualMap_apply']
      exact hingeRow_collapseTo_comp_extProj_eq ha_t u v r'
    have hrowF : BodyHingeFramework.hingeRow u v r' ∈ F.rigidityRows := by
      simp only [BodyHingeFramework.rigidityRows, Set.mem_setOf_eq]
      exact ⟨e', u, v, hFg ▸ hGlink, r', hr'F, rfl⟩
    -- Dmap(hingeRow u' v' r') = Dmap(hingeRow u v r') ∈ Dmap '' F.rigidityRows.
    exact ⟨BodyHingeFramework.hingeRow u v r', hrowF, hrow_eq.symm⟩
  -- ── Step 10: Apply splice brick ──────────────────────────────────────────────────────────
  have hbrick := BodyHingeFramework.le_finrank_span_rigidityRows_of_splice F FH Fc_fw Dmap
    hFH_le hFH_ker hFc_surv_le hInj
  -- ── Step 11: B2 upper bound ──────────────────────────────────────────────────────────────
  have hFext : ∀ e u v, F.graph.IsLink e u v → F.supportExtensor e ≠ 0 := by
    intro e u v hl
    simp only [F, extF]
    split_ifs with h1 h2
    · exact hCe_ne
    · exact hCf_ne
    · -- e is a surviving edge; extF e = Fc_fw.supportExtensor e.
      -- Show (G.rigidContract H' a).IsLink e u v and use hFcext.
      have hclink : (G.rigidContract H' a).IsLink e
          (Graph.collapseTo a V(H') u) (Graph.collapseTo a V(H') v) := by
        rw [Graph.rigidContract, Graph.map_isLink]
        refine ⟨u, v, ?_, rfl, rfl⟩
        rw [Graph.deleteEdges_isLink]
        exact ⟨hFg ▸ hl, by rw [hEH']; simp [h1, h2]⟩
      exact (hFcext e _ _ hclink).1
  have hFVne : V(F.graph).Nonempty := by
    rw [hFg]; exact (Set.ncard_pos (Set.toFinite _)).mp (by omega)
  have hB2 := F.finrank_span_rigidityRows_add_deficiency_le hn hFVne hFext
  -- ── Step 12: Fc finrank from IH ──────────────────────────────────────────────────────────
  have hFcfinrank : (Module.finrank ℝ (Submodule.span ℝ Fc_fw.rigidityRows) : ℤ)
      = screwDim 2 * ((V(G.rigidContract H' a).ncard : ℤ) - 1) - k := by
    rw [hFcrank]; congr 1; rw [hKmin.1]
  -- ── Step 13: Arithmetic to get rank = D(|V|−1) − k ──────────────────────────────────────
  have hVcard : (V(G).ncard : ℤ) = (V(G.rigidContract H' a).ncard : ℤ) + 1 := by
    have := hKcard; omega
  have hrank_eq : (Module.finrank ℝ (Submodule.span ℝ F.rigidityRows) : ℤ)
      = screwDim 2 * ((V(G).ncard : ℤ) - 1) - k := by
    have hbrickZ : (Module.finrank ℝ (Submodule.span ℝ FH.rigidityRows) : ℤ) +
        (Module.finrank ℝ (Submodule.span ℝ Fc_fw.rigidityRows) : ℤ) ≤
        (Module.finrank ℝ (Submodule.span ℝ F.rigidityRows) : ℤ) := by
      exact_mod_cast hbrick
    have hB2' : (Module.finrank ℝ (Submodule.span ℝ F.rigidityRows) : ℤ)
        ≤ screwDim 2 * ((V(G).ncard : ℤ) - 1) - k := by
      have := hB2; rw [hG.1, hFg] at this; linarith
    have hlb : screwDim 2 * ((V(G).ncard : ℤ) - 1) - k ≤
        (Module.finrank ℝ (Submodule.span ℝ F.rigidityRows) : ℤ) := by
      rw [hFH_finrank, hFcfinrank] at hbrickZ
      rw [hVcard]; linarith
    linarith
  -- ── Step 14: hlinks — nonzero + ExtensorInPanel for all G-edges ──────────────────────────
  have hlinks : ∀ e u v, G.IsLink e u v → F.supportExtensor e ≠ 0 ∧
      ExtensorInPanel (F.supportExtensor e) (normal u) ∧
      ExtensorInPanel (F.supportExtensor e) (normal v) := by
    intro e u v hl
    simp only [F, extF]
    split_ifs with h1 h2
    · -- e = e_edge: Ce ∈ (normal a)^⊥. Need to show normal u = normal a and normal v = normal a.
      -- From h1 : e = e_edge and hl : G.IsLink e u v and hle : G.IsLink e_edge a b,
      -- we get {u, v} = {a, b} (up to swap).
      subst h1
      rcases hl.eq_and_eq_or_eq_and_eq hle with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨hCe_ne, hCe_perp, hn_b_eq ▸ hCe_perp⟩
      · exact ⟨hCe_ne, hn_b_eq ▸ hCe_perp, hCe_perp⟩
    · -- e = f_edge: Cf ∈ (normal a)^⊥.
      subst h2
      rcases hl.eq_and_eq_or_eq_and_eq hlf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨hCf_ne, hCf_perp, hn_b_eq ▸ hCf_perp⟩
      · exact ⟨hCf_ne, hn_b_eq ▸ hCf_perp, hCf_perp⟩
    · -- Surviving edge: extF e = Fc_fw.supportExtensor e.
      -- Build the contracted link:
      -- (G.rigidContract H' a).IsLink e (collapseTo a t u) (collapseTo a t v).
      have hclink : (G.rigidContract H' a).IsLink e
          (Graph.collapseTo a t u) (Graph.collapseTo a t v) := by
        rw [Graph.rigidContract, Graph.map_isLink]
        refine ⟨u, v, ?_, rfl, rfl⟩
        rw [Graph.deleteEdges_isLink]
        refine ⟨hl, ?_⟩
        rw [hEH']; simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]; exact ⟨h1, h2⟩
      obtain ⟨hne, hpan1, hpan2⟩ := hFcext e _ _ hclink
      exact ⟨hne, hpan1, hpan2⟩
  -- ── Step 15: Return the realization ──────────────────────────────────────────────────────
  rw [← hG.1] at hrank_eq
  exact ⟨F, normal, rfl, hnorm_ne, hlinks, hrank_eq⟩

end CombinatorialRigidity.Molecular
