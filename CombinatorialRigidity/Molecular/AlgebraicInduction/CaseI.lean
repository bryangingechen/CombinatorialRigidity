/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.AlgebraicInduction.GenericityDevice
import CombinatorialRigidity.Mathlib.RingTheory.MvPolynomial.Tower
import CombinatorialRigidity.Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis

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
      (PanelHingeFramework.ofNormals Gc ends qc).toBodyHinge.IsInfinitesimallyRigidOn V(Gc)) :
    PanelHingeFramework.HasGenericFullRankRealization k G := by
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
    (fun e _ _ _ => hends e) hgp halg hGH hGc hcH hcc hcover hrigH₀ hrigc₀

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
theorem PanelHingeFramework.rigidContract_rigidity_transport
    (G H : Graph α β) (ends : β → α × α) {r : α}
    (hQ : PanelHingeFramework.HasGenericFullRankRealization k (G.rigidContract H r))
    (htransport : ∀ Q : PanelHingeFramework k α β, Q.graph = G.rigidContract H r →
      Q.IsGeneralPosition →
      Q.toBodyHinge.IsInfinitesimallyRigidOn V(G.rigidContract H r) →
      ∃ q_c : α × Fin (k + 2) → ℝ,
        (PanelHingeFramework.ofNormals (G.deleteEdges E(H)) ends q_c).toBodyHinge
          |>.IsInfinitesimallyRigidOn ((V(G) \ V(H)) ∪ {r})) :
    ∃ q_c : α × Fin (k + 2) → ℝ,
      (PanelHingeFramework.ofNormals (G.deleteEdges E(H)) ends q_c).toBodyHinge
        |>.IsInfinitesimallyRigidOn ((V(G) \ V(H)) ∪ {r}) :=
  let ⟨Q, hQg, hQgp, hQrig, _⟩ := hQ
  htransport Q hQg hQgp hQrig

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
* both legs are nonempty (`V(H)` nonempty by hypothesis; `V(G ＼ E(H)) = V(G) ∋ r`).

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
  obtain ⟨⟨hle, _⟩, hVHne, hVHss⟩ := hH
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
      (PanelHingeFramework.ofNormals Gc ends q₀).toBodyHinge.IsInfinitesimallyRigidOn sc) :
    PanelHingeFramework.HasGenericFullRankRealization k G :=
  -- The witness is the seed framework itself; rigidity on `V(G)` is the genericity-free body-set
  -- splice glue (no device round-trip, so general position of `q₀` survives), GP is `hgp`, the
  -- link-recording conjunct is the seed selector's link-recording (`hends`), and the
  -- algebraic-independence conjunct is `halg`.
  ⟨PanelHingeFramework.ofNormals G ends q₀, PanelHingeFramework.ofNormals_graph G ends q₀, hgp,
    (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.isInfinitesimallyRigidOn_of_splice
      (GH := GH) (Gc := Gc) (sH := sH) (sc := sc) hGH hGc hcH hcc hcover hblock hcontract,
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
      (PanelHingeFramework.ofNormals Gc ends qc).toBodyHinge.IsInfinitesimallyRigidOn sc) :
    PanelHingeFramework.HasGenericFullRankRealization k G := by
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
    halg hGH hGc hcH hcc hcover hrigH₀ hrigc₀

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
      (PanelHingeFramework.ofNormals Gc ends q).toBodyHinge.IsInfinitesimallyRigidOn sc) :
    PanelHingeFramework.HasGenericFullRankRealization k G := by
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
    halg hGH hGc hcH hcc hcover hrigH₀ hrigc₀

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
    (Gc : Graph α β) (f : α → α) (ends : β → α × α)
    (Qcf : PanelHingeFramework.HasGenericFullRankRealization k (Gc.map f))
    (hends : ∀ e u v, Gc.IsLink e u v → Gc.IsLink e (ends e).1 (ends e).2) :
    ∃ nrm : α × Fin (k + 2) → ℝ,
      (PanelHingeFramework.ofNormals (Gc.map f)
        (fun e => (f (ends e).1, f (ends e).2)) nrm).IsGeneralPosition ∧
      (PanelHingeFramework.ofNormals (Gc.map f)
        (fun e => (f (ends e).1, f (ends e).2)) nrm).toBodyHinge.IsInfinitesimallyRigidOn
        V(Gc.map f) := by
  obtain ⟨Q, hQg, hQgp, hQrig, hQrec, _⟩ := Qcf
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
    (hQ : PanelHingeFramework.HasGenericFullRankRealization k (G.rigidContract H r))
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
            ends (i : β × _ × _))) :=
  let ⟨Q, hQg, hQgp, hQrig, _⟩ := hQ
  htransport Q hQg hQgp hQrig

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
    (hQcf : PanelHingeFramework.HasGenericFullRankRealization k (G.rigidContract H r))
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
    PanelHingeFramework.hasGenericRealization_transport_relabel Gc f ends hQcf hends
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

/-- **An independent family of rigidity rows of size `≥ D(|V(G)|−1)` forces rigidity on `V(G)`**
(`lem:case-I-realization`, the device-row-addition closure; Katoh–Tanigawa 2011 §6.2 eq. (6.3),
Phase 22a). The block-triangular reframing's device-side closure (design doc §1.14): rather than
gluing two legs at a *common seed* (the motion-space splice `isInfinitesimallyRigidOn_of_splice`,
which demands one placement rigid on both legs), exhibit enough **independent rigidity rows** of the
single common framework `F` and read rigidity off the row count. From any linearly independent
family `a : ι → Module.Dual ℝ (α → ScrewSpace k)` of `F`'s rigidity rows (each
`a i ∈ rigidityRows F`, `hmem`) with `Nat.card ι ≥ D(|V(G)|−1)` (`hcard`), the rank-nullity identity
`dim Z(F) = D|V| − finrank (span rigidityRows) ≤ D|V| − D(|V|−1) = D` upgrades, via the
relative-count adapter N3 (`isInfinitesimallyRigidOn_vertexSet_of_finrank_le`), to infinitesimal
rigidity on `V(G)`.

This is the same rank-nullity argument the rank-polynomial consumer
`isInfinitesimallyRigidOn_ofNormals_of_rankPolynomial_ne_zero_linking` runs, but over an *arbitrary*
finite index family rather than a `Set`-subfamily, so the **block-triangular union** of the
`H`-block and surviving-edge rows (`Sum.elim`, Piece B) feeds it directly. Crucially it concludes
rigidity of `F` *itself* (at its own seed), so when `F = ofNormals G ends q₀` with `q₀` general
position the conclusion lifts to the *generic* motive — no device round-trip, general position
survives. -/
theorem BodyHingeFramework.isInfinitesimallyRigidOn_vertexSet_of_independent_rigidityRows
    [Finite α] (F : BodyHingeFramework k α β) {ι : Type*} [Finite ι]
    {a : ι → Module.Dual ℝ (α → ScrewSpace k)} (hLI : LinearIndependent ℝ a)
    (hmem : ∀ i, a i ∈ F.rigidityRows) (hne : F.graph.vertexSet.Nonempty)
    (hcard : screwDim k * (F.graph.vertexSet.ncard - 1) ≤ Nat.card ι) :
    F.IsInfinitesimallyRigidOn F.graph.vertexSet := by
  classical
  haveI : Fintype α := Fintype.ofFinite α
  haveI : Fintype ι := Fintype.ofFinite ι
  -- The independent family spans a subspace of the rigidity-row span of dimension `Nat.card ι`.
  have hsub : Submodule.span ℝ (Set.range a) ≤ Submodule.span ℝ F.rigidityRows :=
    Submodule.span_le.2 (fun _ ⟨i, hi⟩ => hi ▸ Submodule.subset_span (hmem i))
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
          ((PanelHingeFramework.ofNormals G ends q).toBodyHinge.panelRow ends (i : β × _ × _)))) :
    PanelHingeFramework.HasGenericFullRankRealization k G := by
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
  exact hrig

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
      (G'.Simple → PanelHingeFramework.HasGenericFullRankRealization k G') ∧
        PanelHingeFramework.HasFullRankRealization k G') :
    PanelHingeFramework.HasGenericFullRankRealization k G := by
  classical
  haveI : NeZero (Graph.bodyHingeMult n) := ⟨by rw [Graph.bodyHingeMult]; omega⟩
  obtain ⟨⟨hle, hKDof⟩, hVHne, hVHss⟩ := hH
  have hHsub : V(H) ⊆ V(G) := hle.vertexSet_mono
  have hVHlt : V(H).ncard < V(G).ncard := Set.ncard_lt_ncard hVHss (Set.toFinite _)
  -- Manufacture the parent endpoint selector from `G` alone via the canonical `endsOf` (G3c-iii-a):
  -- it links every edge (`isLink_endsOf`), exactly the edge-restricted `hends` the body-set generic
  -- coupling needs (the all-`β` form is unsatisfiable for a label type with non-edges).
  haveI : Inhabited α := ⟨r⟩
  set ends := G.endsOf with hendsDef
  have hends : ∀ e u v, G.IsLink e u v → G.IsLink e (ends e).1 (ends e).2 := by
    rw [hendsDef]; exact fun e _ _ h => G.isLink_endsOf h.edge_mem
  have hHprop : H.IsProperRigidSubgraph G n := ⟨⟨hle, hKDof⟩, hVHne, hVHss⟩
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
  obtain ⟨QH, hQHg, hQHgp, hQHrig, hQHrec, _⟩ :=
    (hIH H hHmin hVH2 hVHlt).1 (hSimple.mono hle)
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
  have hQcf : PanelHingeFramework.HasGenericFullRankRealization k (G.rigidContract H r) :=
    (hIH (G.rigidContract H r) hKmin hK2 hKlt).1 hcSimple
  obtain ⟨q₀, t, hsupp, hcount, hindep⟩ :=
    PanelHingeFramework.rigidContract_exterior_rank_transport (k := k) G H ends hQcf
      (PanelHingeFramework.rigidContract_exterior_rank_transport_htransport G H ends hr hHsub
        hcSimple hQcf hendsGc)
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
    ⟨r, hHsub hr⟩ ⟨r, hr⟩ le_rfl (qH := qH) hneH hrigH Qc hQc_ne hQc_rat hsc_proj_indep

/-- **The device's coordinatization from a spanning enumeration of one realization's rigidity
rows** (`lem:genericity-device`, the route-(a) closure for Case I; Phase 21b). The route-(a)
resolution the hand-off flagged: the witness realization Case I needs is *constructed directly* by
the exterior-algebra existence lemma `exists_independent_panelSupportExtensor` (a basis choice on
`⋀²`, Phase 21/17), not found by perturbing along a path through panel-coordinate space. So the
multivariate family the device consumes can be the **constant** family `F p = F₀`, with `g p = a`
any family **spanning** the rigidity rows of the single good realization `F₀` (`hspanrows`); the
bilinearity obstruction (the panel rows are quadratic along a real line through normal-space) never
bites, because no path is traversed — the device reads off the corank `#s` at the one hand-built
realization, which is all Case I's block-triangular gluing needs.

This packages the constant family into the multivariate `exists_good_realization`: the
panel-coordinate variables `σ := Unit` are vacuous (the framework does not vary), the polynomial
coordinates are the constants `c i j = C (φ (a i) j)` (so `hg` is `eval_C`), and the
coordinatization `hcoord` is the per-framework `infinitesimalMotions_eq_dualCoannihilator` rewritten
under `hspanrows`. The basis identification `φ` is taken from any finite basis of the
finite-dimensional dual `α → ScrewSpace k` (`Module.finBasis … |>.equivFun`). The output is the
unquantified codimension bound `#s + dim Z(F₀) ≤ D|V|` at `F₀` itself — the form
`hglue_of_realization` consumes. The independent subfamily `s` (the engine's `hindep`) is supplied
by `exists_independent_panelSupportExtensor` through the hinge-row block. -/
theorem exists_good_realization_const [Fintype α] {ι : Type*} [Finite ι]
    (F₀ : BodyHingeFramework k α β) (a : ι → Module.Dual ℝ (α → ScrewSpace k))
    (hspanrows : Submodule.span ℝ (Set.range a) = Submodule.span ℝ F₀.rigidityRows)
    {s : Set ι} (hindep : LinearIndependent ℝ (fun i : s => a i)) :
    Nat.card s + Module.finrank ℝ F₀.infinitesimalMotions ≤ screwDim k * Fintype.card α := by
  classical
  set n := Module.finrank ℝ (Module.Dual ℝ (α → ScrewSpace k)) with hn
  -- A basis identification of the finite-dimensional dual with `Fin n → ℝ`.
  let φ : Module.Dual ℝ (α → ScrewSpace k) ≃ₗ[ℝ] (Fin n → ℝ) :=
    (Module.finBasis ℝ (Module.Dual ℝ (α → ScrewSpace k))).equivFun
  -- The constant family: `F p = F₀`, rows `g p = a`, polynomial coords the constants `φ (a i) j`.
  obtain ⟨p, hp⟩ := exists_good_realization (σ := Unit) (s := s) (p₀ := fun _ => 0)
    (fun _ => F₀) (fun _ => a) (fun i j => MvPolynomial.C (φ (a i) j)) φ
    (fun _ i j => by rw [MvPolynomial.eval_C])
    (fun _ => le_of_eq (by rw [F₀.infinitesimalMotions_eq_dualCoannihilator, hspanrows]))
    hindep
  exact hp

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
  have ht := exists_good_realization_const F₀ a hspanrows hindep
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
  `rigidityMatrix_prop11` (every realization carries at least `D + def` motions).

`rigidityMatrix_prop11` pins the equality from the two. The independent family `s` comes from
`G_v`'s minimal-`k'`-dof IH realization run through the device producer, supplying the rational
rank polynomial `Q` (`hQrat`/`hQne`/`hQ`) whose non-roots witness `s` (its edges linking in `G`,
`hsupp`); the alg-independence of the fixed seed `q` (`halg`) makes `q` a non-root *at the fixed
seed itself* (footnote 6). It is honest per the producer-scrutiny gate: the witnessed-rank input
`Q` is an unrelated rigid seed's rank certificate, not the rank concluded; `hub` is the
genericity-free lower bound carried (as in `rigidityMatrix_prop11`) as an explicit hypothesis. -/
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
    (hub : screwDim k + G.deficiency n ≤
      (Module.finrank ℝ (PanelHingeFramework.ofNormals G ends q).toBodyHinge.infinitesimalMotions :
        ℤ)) :
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
  -- `rigidityMatrix_prop11` pins the equality from `hub` (lower) and `hgen` (upper).
  exact rigidityMatrix_prop11 F n hub hgen

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

end CombinatorialRigidity.Molecular
