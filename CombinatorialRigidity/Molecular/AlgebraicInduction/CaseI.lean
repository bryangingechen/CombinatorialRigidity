/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.AlgebraicInduction.GenericityDevice

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
  obtain ⟨sH, QH, hsuppH, hcardH, hQ0H, hLIH⟩ :=
    PanelHingeFramework.exists_rankPolynomial_of_rigidOn_linking GH ends hendsH hneH hnevH hrigH
  obtain ⟨sc, Qc, hsuppc, hcardc, hQ0c, hLIc⟩ :=
    PanelHingeFramework.exists_rankPolynomial_of_rigidOn_linking Gc ends hendsc hnec hnevc hrigc
  -- (ii) The general-position factor: nonzero (witnessed at a moment-curve seed), non-roots general
  -- position.
  obtain ⟨Qgp, hQgp_ne, hQgp_pos⟩ :=
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
  -- Steps (i)–(iv) are identical to the bare coupling: a shared non-root `q₀` of the triple
  -- product (each leg's leg-restricted rank polynomial × the general-position factor) at which
  -- both legs are rigid and the parent normals are in general position.
  have hendsH : ∀ e u v, GH.IsLink e u v → GH.IsLink e (ends e).1 (ends e).2 := fun e _ _ h =>
    (Graph.IsSubgraph.isLink_iff hGH h.edge_mem).mpr (hends e)
  have hendsc : ∀ e u v, Gc.IsLink e u v → Gc.IsLink e (ends e).1 (ends e).2 := fun e _ _ h =>
    (Graph.IsSubgraph.isLink_iff hGc h.edge_mem).mpr (hends e)
  obtain ⟨sH, QH, hsuppH, hcardH, hQ0H, hLIH⟩ :=
    PanelHingeFramework.exists_rankPolynomial_of_rigidOn_linking GH ends hendsH hneH hnevH hrigH
  obtain ⟨sc, Qc, hsuppc, hcardc, hQ0c, hLIc⟩ :=
    PanelHingeFramework.exists_rankPolynomial_of_rigidOn_linking Gc ends hendsc hnec hnevc hrigc
  obtain ⟨Qgp, hQgp_ne, hQgp_pos⟩ :=
    exists_generalPosition_polynomial (k := k) G ends
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
  -- (v') The generic splice: realize at the GP seed `q₀` itself (bypassing the device), so general
  -- position survives and the conclusion is the strengthened generic motive.
  exact PanelHingeFramework.hasGenericFullRankRealization_of_splice_ofNormals G ends hgp
    hGH hGc hcH hcc hcover hrigH₀ hrigc₀

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
  obtain ⟨rsH, QH, hsuppH, hcardH, hQ0H, hLIH⟩ :=
    PanelHingeFramework.exists_rankPolynomial_of_rigidOn_linking_set GH ends hendsH hneH hnesH hrigH
  obtain ⟨rsc, Qc, hsuppc, hcardc, hQ0c, hLIc⟩ :=
    PanelHingeFramework.exists_rankPolynomial_of_rigidOn_linking_set Gc ends hendsc hnec hnesc hrigc
  -- (ii) The general-position factor.
  obtain ⟨Qgp, hQgp_ne, hQgp_pos⟩ :=
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
`ofNormals GH ends qH` is again in general position; for any edge whose `ends`-endpoints are
distinct (`hne_ends`), `supportExtensor_ne_zero_of_isGeneralPosition` gives the transversal hinge
`hneH`.

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
    (hne_ends : ∀ e, (ends e).1 ≠ (ends e).2) :
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
  refine ⟨qH, fun e _ =>
    (PanelHingeFramework.ofNormals Q.graph ends qH).supportExtensor_ne_zero_of_isGeneralPosition
      hgp' (by rw [PanelHingeFramework.ofNormals_ends]; exact hne_ends e), ?_⟩
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
  let ⟨Q, hQg, hQgp, hQrig⟩ := hQ
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
    {q₀ : α × Fin (k + 2) → ℝ}
    (hgp : (PanelHingeFramework.ofNormals G ends q₀).IsGeneralPosition)
    {GH Gc : Graph α β} (hGH : GH ≤ G) (hGc : Gc ≤ G)
    {sH sc : Set α} {c : α} (hcH : c ∈ sH) (hcc : c ∈ sc) (hcover : V(G) ⊆ sH ∪ sc)
    (hblock : (PanelHingeFramework.ofNormals GH ends q₀).toBodyHinge.IsInfinitesimallyRigidOn sH)
    (hcontract :
      (PanelHingeFramework.ofNormals Gc ends q₀).toBodyHinge.IsInfinitesimallyRigidOn sc) :
    PanelHingeFramework.HasGenericFullRankRealization k G :=
  -- The witness is the seed framework itself; rigidity on `V(G)` is the genericity-free body-set
  -- splice glue (no device round-trip, so general position of `q₀` survives), GP is `hgp`.
  ⟨PanelHingeFramework.ofNormals G ends q₀, PanelHingeFramework.ofNormals_graph G ends q₀, hgp,
    (PanelHingeFramework.ofNormals G ends q₀).toBodyHinge.isInfinitesimallyRigidOn_of_splice
      (GH := GH) (Gc := Gc) (sH := sH) (sc := sc) hGH hGc hcH hcc hcover hblock hcontract⟩

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
  -- (i) Each leg's *body-set* leg-restricted rank polynomial at its own seed.
  obtain ⟨rsH, QH, hsuppH, hcardH, hQ0H, hLIH⟩ :=
    PanelHingeFramework.exists_rankPolynomial_of_rigidOn_linking_set GH ends hendsH hneH hnesH hrigH
  obtain ⟨rsc, Qc, hsuppc, hcardc, hQ0c, hLIc⟩ :=
    PanelHingeFramework.exists_rankPolynomial_of_rigidOn_linking_set Gc ends hendsc hnec hnesc hrigc
  -- (ii) The general-position factor.
  obtain ⟨Qgp, hQgp_ne, hQgp_pos⟩ :=
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
  -- (v) The *generic* body-set splice: realize at the GP seed `q₀` itself (bypassing the device),
  -- so general position survives and the conclusion is the strengthened generic motive.
  exact PanelHingeFramework.hasGenericFullRankRealization_of_splice_set_ofNormals G ends hgp
    hGH hGc hcH hcc hcover hrigH₀ hrigc₀

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
  -- (i) The `H`-leg's body-set leg-restricted rank polynomial at its own seed.
  obtain ⟨rsH, QH, hsuppH, hcardH, hQ0H, hLIH⟩ :=
    PanelHingeFramework.exists_rankPolynomial_of_rigidOn_linking_set GH ends hendsH hneH hnesH hrigH
  -- (ii) The general-position factor.
  obtain ⟨Qgp, hQgp_ne, hQgp_pos⟩ :=
    exists_generalPosition_polynomial (k := k) G ends
  -- (iii) The product `Q_H · Q_gp` has a shared non-root `q₀` (only the H-leg + GP factors now).
  have hQHne : QH ≠ 0 := fun h => hQ0H (by rw [h, map_zero])
  have hQgpne : Qgp ≠ 0 := by
    obtain ⟨f, hf⟩ := Countable.exists_injective_nat α
    refine fun h => hQgp_ne (fun a => (f a : ℝ)) ?_ (by rw [h, map_zero])
    exact fun a b hab => hf (Nat.cast_injective hab)
  obtain ⟨q₀, hq₀⟩ := MvPolynomial.exists_eval_ne_zero (mul_ne_zero hQHne hQgpne)
  rw [map_mul] at hq₀
  have hq₀H : MvPolynomial.eval q₀ QH ≠ 0 := fun h => hq₀ (by rw [h]; ring)
  have hq₀gp : MvPolynomial.eval q₀ Qgp ≠ 0 := fun h => hq₀ (by rw [h]; ring)
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
  -- (v) The generic body-set splice: realize at the GP seed `q₀` itself.
  exact PanelHingeFramework.hasGenericFullRankRealization_of_splice_set_ofNormals G ends hgp
    hGH hGc hcH hcc hcover hrigH₀ hrigc₀

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
  -- The projected evaluation identity: each projected coordinate is the polynomial `cD`.
  have hgD : ∀ q i j, φ (gD q i) j = MvPolynomial.eval q (cD i j) := by
    intro q i j
    rw [hgD_def, hMrep, hcD_def, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_mul, MvPolynomial.eval_C, hg]
  -- Extract the witnessing rank polynomial via the engine on the projected family, re-phrase.
  obtain ⟨Q, hQ₀, hQ⟩ :=
    exists_polynomial_ne_zero_of_linearIndependent_at gD cD φ hgD (p₀ := q₀) (s := t)
      (by simpa only [hgD_def, hg_def, hDdef] using hindep)
  refine ⟨Q, fun hQz => hQ₀ (by rw [hQz, map_zero]), fun q hq => ?_⟩
  exact ⟨t, hsupp, hcount, by simpa only [hgD_def, hg_def, hDdef] using hQ q hq⟩

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
  -- (i) The `H`-leg's body-set leg-restricted rank polynomial at its own seed `qH`. Each witnessed
  -- index links in `GH` (`hsuppH`), so both its endpoints lie in `V(GH) ⊆ sH`.
  obtain ⟨rsH, QH, hsuppH, hcardH, hQ0H, hLIH⟩ :=
    PanelHingeFramework.exists_rankPolynomial_of_rigidOn_linking_set GH ends hendsH hneH hnesH hrigH
  -- (ii) The general-position factor.
  obtain ⟨Qgp, hQgp_ne, hQgp_pos⟩ :=
    exists_generalPosition_polynomial (k := k) G ends
  -- (iii) The **triple** product `Q_H · Q_c · Q_gp` has a shared non-root `q₀` (H-block LI +
  -- the contraction rank polynomial `Q_c`'s generic locus + general position).
  have hQHne : QH ≠ 0 := fun h => hQ0H (by rw [h, map_zero])
  have hQgpne : Qgp ≠ 0 := by
    obtain ⟨f, hf⟩ := Countable.exists_injective_nat α
    refine fun h => hQgp_ne (fun a => (f a : ℝ)) ?_ (by rw [h, map_zero])
    exact fun a b hab => hf (Nat.cast_injective hab)
  obtain ⟨q₀, hq₀⟩ := MvPolynomial.exists_eval_ne_zero
    (mul_ne_zero (mul_ne_zero hQHne hQc_ne) hQgpne)
  rw [map_mul, map_mul] at hq₀
  have hq₀H : MvPolynomial.eval q₀ QH ≠ 0 := fun h => hq₀ (by rw [h]; ring)
  have hq₀c : MvPolynomial.eval q₀ Qc ≠ 0 := fun h => hq₀ (by rw [h]; ring)
  have hq₀gp : MvPolynomial.eval q₀ Qgp ≠ 0 := fun h => hq₀ (by rw [h]; ring)
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
  -- `q₀` general position the strengthened generic motive holds. The witness is `F`.
  refine ⟨PanelHingeFramework.ofNormals G ends q₀,
    PanelHingeFramework.ofNormals_graph G ends q₀, hgp, ?_⟩
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
  irreducibly research-shaped (the collapse redirects each surviving edge's endpoints, so no green
  brick converts the relabelled-contraction rank into the surviving-edge rank — the G3a finding). It
  is carried as the conjunct `hclaim64` of the explicit bundle `hbundle`, stated as a **rank
  polynomial** `Qc ≠ 0` whose non-roots carry **exterior-column-projected row-independence**: at
  every `Qc`-non-root seed (the Zariski-open generic locus of KT eq. (6.9), *not* every
  general-position seed), the surviving rows are `≥ D(|sc|−1)` and independent after projecting away
  the rigid-block columns `V(H)` (`(extProj V(H)).dualMap`) — KT's bottom-right block rank. The
  `H`-leg's selector alignment `hswap`/`hne_ends` is the KT eq. (6.6) placement, the other bundle
  conjunct.

The block-triangular coupling exhibits `D(|V(G)|−1)` independent rigidity rows of the *single*
common framework `ofNormals G ends q₀` — the `H`-block rows (which vanish under the exterior-column
projection, KT's top-right `0`) `⊔` the surviving-edge rows (the projected block) — and reads
rigidity on `V(G)` off the row count via the device-row closure, *at `q₀` itself*; since `q₀` is
general position the strengthened motive holds. **This needs no common placement rigid on both
legs** (the §1.13 impasse the asymmetric coupling could not cross): the device counts independent
*rows*, never rigidity of one framework on a leg at a shared seed.

**Green-modulo the Claim-6.4 bundle** (`hbundle` + `hcSimple`, the Phase-21b green-modulo `h…`
idiom, discharged by `lem:case-III` / 22b+): the only modulo-content is the single
KT-eq. (6.5)/(6.9) exterior-projected row-independence, carried as the `Qc`-non-root form `hclaim64`
(a contraction rank polynomial `Qc ≠ 0` whose non-roots carry the projected independence — KT
eq. (6.9)'s generic locus), a contraction-leg-local row-count (not the undischargeable `∀`-GP-rigid
`htransportGP` the asymmetric coupling needed, nor the over-quantified `∀`-GP-independent form §1.16
flagged, nor a false pin-equality) — every step the composer itself performs is honest, not a
`sorry`. -/
theorem PanelHingeFramework.case_I_realization [DecidableEq β] [Finite α] [Finite β] {n k : ℕ}
    (hD : 3 ≤ Graph.bodyBarDim n)
    (G : Graph α β) (hG : G.IsMinimalKDof n 0)
    {H : Graph α β} (hH : H.IsProperRigidSubgraph G n) {r : α} (hr : r ∈ V(H))
    (hVH2 : 2 ≤ V(H).ncard) (hSimple : G.Simple)
    (hcSimple : (G.rigidContract H r).Simple)
    (hIH : ∀ G' : Graph α β, G'.IsMinimalKDof n 0 → 2 ≤ V(G').ncard →
      V(G').ncard < V(G).ncard →
      (G'.Simple → PanelHingeFramework.HasGenericFullRankRealization k G') ∧
        PanelHingeFramework.HasFullRankRealization k G')
    -- The Claim-6.4 + placement bundle (KT eqs. (6.6), (6.5)/(6.9); design doc §1.14/§1.16),
    -- carried in the Phase-21b green-modulo `h…` idiom against the manufactured parent selector
    -- `ends` and the chosen `H`/`r`. It supplies (a) the `H`-leg selector alignment
    -- `hswap`/`hne_ends` that `hasGenericRealization_transport_ends` consumes (KT eq. (6.6)), and
    -- (b) the contraction leg's Claim-6.4 transport as a **rank polynomial** `Qc ≠ 0` whose
    -- non-roots carry **exterior-column-projected row-independence** (KT's bottom-right block rank
    -- `rank R(G,p; E∖E′, V∖V′) = D(|sc|−1)`, eqs. (6.5)/(6.9)): given the contraction's generic IH
    -- `Q`, at *every `Qc`-non-root* parent seed (the Zariski-open generic locus of KT eq. (6.9),
    -- NOT every general-position seed) the surviving rows of `G ＼ E(H)` are `≥ D(|sc|−1)` and
    -- independent after projecting away the rigid-block columns `V(H)` (`(extProj V(H)).dualMap`).
    -- This is the single dischargeable Claim-6.4 row-count (design doc §1.16), *not* the
    -- undischargeable `∀`-GP-rigid `htransportGP` nor the over-quantified `∀`-GP-independent form.
    (hbundle : ∀ ends : β → α × α,
      (∀ Q : PanelHingeFramework k α β, Q.graph = H →
        (∀ e u v, H.IsLink e u v →
          ((Q.ends e).1 = (ends e).1 ∧ (Q.ends e).2 = (ends e).2) ∨
          ((Q.ends e).1 = (ends e).2 ∧ (Q.ends e).2 = (ends e).1))) ∧
      (∀ e, (ends e).1 ≠ (ends e).2) ∧
      (∀ Q : PanelHingeFramework k α β, Q.graph = G.rigidContract H r →
        Q.IsGeneralPosition →
        Q.toBodyHinge.IsInfinitesimallyRigidOn V(G.rigidContract H r) →
        ∃ Qc : MvPolynomial (α × Fin (k + 2)) ℝ, Qc ≠ 0 ∧
          ∀ q : α × Fin (k + 2) → ℝ, MvPolynomial.eval q Qc ≠ 0 →
          ∃ rsc : Set (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k),
            (∀ i ∈ rsc, (G.deleteEdges E(H)).IsLink (i : β × _ × _).1
              (ends (i : β × _ × _).1).1 (ends (i : β × _ × _).1).2) ∧
            screwDim k * (((V(G) \ V(H)) ∪ {r}).ncard - 1) ≤ Nat.card rsc ∧
            LinearIndependent ℝ (fun i : rsc => (extProj (k := k) V(H)).dualMap
              ((PanelHingeFramework.ofNormals G ends q).toBodyHinge.panelRow ends
                (i : β × _ × _))))) :
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
  obtain ⟨hswap, hne_ends, hclaim64⟩ := hbundle ends
  -- The geometric inputs of the coupling for legs `H` / `G ＼ E(H)` sharing `r` (G3b); the cover is
  -- against the *surviving-body* set `sc := (V(G)∖V(H)) ∪ {r}` (its `(V(G)∖V(H))` part alone
  -- complements `V(H)`).
  obtain ⟨hGH, hGc, _, _, _, _, _⟩ :=
    PanelHingeFramework.couple_geometry_of_isProperRigidSubgraph hHprop hr
  have hcover : V(G) ⊆ V(H) ∪ ((V(G) \ V(H)) ∪ {r}) := by
    intro x hx
    by_cases hxH : x ∈ V(H)
    · exact Or.inl hxH
    · exact Or.inr (Or.inl ⟨hx, hxH⟩)
  -- (1) The `H`-leg: extract its generic IH and transport it to the parent selector (rigid +
  -- transversal on its *full* `V(H)`). The block-triangular coupling uses only the `H`-block *rows*
  -- (the `H`-leg rank polynomial), so no complement-isolation equality is needed for this leg.
  have hHmin : H.IsMinimalKDof n 0 := Graph.subgraph_minimality hle hG hKDof
  obtain ⟨QH, hQHg, hQHgp, hQHrig⟩ :=
    (hIH H hHmin hVH2 hVHlt).1 (hSimple.mono hle)
  obtain ⟨qH, hneH, hrigH⟩ :=
    PanelHingeFramework.hasGenericRealization_transport_ends H ends QH hQHg hQHgp hQHrig
      (hswap QH hQHg) hne_ends
  -- (2) The `G ＼ E(H)`-leg: the contraction is a smaller, simple minimal `0`-dof-graph (N4 +
  -- `hcSimple`), so `hIH` supplies its generic realization `Qc`. KT Claim 6.4 (eqs. (6.5)/(6.9),
  -- the bundle's `hclaim64`) turns that rank into the surviving edges' **exterior-projected
  -- row-independence** — KT's bottom-right block rank — which the block-triangular coupling reads
  -- as the `s_c` block (no common-seed rigidity, no false complement-isolation equality).
  have hKmin : (G.rigidContract H r).IsMinimalKDof n 0 :=
    Graph.rigidContract_isMinimalKDof hG hHprop hr
  have hKlt : V(G.rigidContract H r).ncard < V(G).ncard :=
    Graph.rigidContract_vertexSet_ncard_lt hHsub hVH2
  have hK2 : 2 ≤ V(G.rigidContract H r).ncard := by
    rw [Graph.rigidContract_vertexSet_ncard hr hHsub]
    have hVHle : V(H).ncard ≤ V(G).ncard := Set.ncard_le_ncard hHsub (Set.toFinite _)
    omega
  obtain ⟨Qcf, hQcfg, hQcfgp, hQcfrig⟩ :=
    (hIH (G.rigidContract H r) hKmin hK2 hKlt).1 hcSimple
  -- KT Claim 6.4 (the bundle's `hclaim64`) turns the contraction's generic IH into a contraction
  -- **rank polynomial** `Qc ≠ 0` such that at every `Qc`-non-root the surviving rows are
  -- exterior-projected independent (the Zariski-open generic locus of KT eq. (6.9), *not* every
  -- general-position seed).
  obtain ⟨Qc, hQc_ne, hsc_proj_indep⟩ := hclaim64 Qcf hQcfg hQcfgp hQcfrig
  -- (3) Feed both legs into the **block-triangular** body-set generic coupling (`sH := V(H)`,
  -- `sc := (V(G)∖V(H))∪{r}`): the `H`-block rows from the rank polynomial, the surviving-edge
  -- block from the Claim-6.4 exterior-projected row-independence at the `Qc`-non-root seed. The
  -- device-row closure reads rigidity on `V(G)` off the joint row count — no common placement
  -- rigid on both legs.
  exact PanelHingeFramework.hasGenericFullRankRealization_of_couple_blockTriangular_ofNormals_set
    G ends hends hGH hGc (sH := V(H)) (sc := (V(G) \ V(H)) ∪ {r}) (c := r) hr (Or.inr rfl) hcover
    ⟨r, hHsub hr⟩ ⟨r, hr⟩ le_rfl (qH := qH) hneH hrigH Qc hQc_ne hsc_proj_indep

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

end CombinatorialRigidity.Molecular
