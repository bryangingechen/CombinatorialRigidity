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
# The algebraic induction — Case I coupling foundations (coupling + `extProj`)

Phase 22 (molecular-conjecture program; see `notes/MolecularConjecture.md`). The foundations head of
the algebraic-induction realization layer, carved off `AlgebraicInduction/CaseI.lean` in the
post-Phase-22j perf round (`notes/Phase22j-perf.md`; no decl renamed or re-namespaced). On top of
the genericity device (`AlgebraicInduction/GenericityDevice`), this file carries the shared base the
Case-I composer and the later cases all build on:

* the **shared-seed / block-triangular coupling** producers
  (`hasFullRankRealization_of_couple…`, `hasGenericFullRankRealization_of_couple…`) — KT eq. 6.3
  rank-addition over one common framework;
* the **exterior-column projection** `extProj` onto the surviving body columns, with its
  apply/range/kernel lemmas;
* the **projection-into-pinned-motions** bridges (`infinitesimalMotions_*_range_extProj_*`,
  `BodyHingeFramework.injOn_extProj_dualMap_rigidityRows…`) and the projected
  independent-subfamily extractors (`exists_independent_panelRow_subfamily_*_proj`).

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
end CombinatorialRigidity.Molecular
