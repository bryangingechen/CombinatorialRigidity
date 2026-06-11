# Phase 22 — realization-layer design (decision-support doc)

> **File-layout note (pre-Phase-22b structure pass, `notes/Phase22-structure.md`).**
> The single files this doc cites have since been split into subdirectories:
> `AlgebraicInduction.lean` → `Molecular/AlgebraicInduction/`
> (`PanelLayer`/`Pinning`/`PanelHinge`/`GenericityDevice`/`CaseI`) and `Induction.lean` →
> `Molecular/Induction/` (`Operations`/`SplitOffDeficiency`/`ReducibleVertex`/`Contraction`/`ForestSurgery`).
> Inline `….lean:NNNN` line anchors below **predate the split** — find declarations by name in
> the relevant sub-file (the Case-I composer `case_I_realization` and the couple / genericity-device
> producers are in `CaseI` / `GenericityDevice`; `minimal_kdof_reduction` is in `Induction/ForestSurgery`).

**Status:** design pass, not a build plan. Produced 2026-06-04 after the
constructibility recon (FRICTION dead-end #5; `notes/Phase22a.md` *Blockers*)
found the Case-I coupling has two real gaps **(G1)/(G2)** the type-level plan
was blind to. The user paused per-commit Lean work to decide the **motive
question** — should `PanelHingeFramework.HasFullRankRealization` carry general
position (KT's "nonparallel"). The motive decision landed (the **two-motive
split**, §1.4, green); §**1.5** (2026-06-04) is the follow-on **generic-motive
recon** settling the N6-composer IH-shape gap as a **hybrid route** and cutting
it into the buildable N6-G1/G2/G3 nodes; §**1.6** (2026-06-04) cuts N6-G2 into
G2a/G2b/G2c (all now green); §**1.7** (2026-06-05) is the **N6-G3 recon**,
settling the `Gc ≤ G` binding obstruction (the splice's contraction leg is
`G ＼ E(H)`, not the relabelled `rigidContract`; the collapse lives on the
placement side as KT's Claim 6.4 transport) and cutting N6-G3 into G3a/G3b/G3c;
§**1.8**–§**1.9** (2026-06-05) re-recon G3c (the body-set mismatch; route (a)),
all green; §**1.10** (2026-06-05) lands G3c-iii's GP-conjunct producer bricks and
cuts the residual assembly into G3c-iii-a/b; §**1.11** (2026-06-05) is the
**G3c-iii-a parent-`ends` impedance recon**, settling it as **option (iii)** (the
producers need only an *edge-restricted* `hends`, supplied by a small
`ends`-existence side-lemma — verified buildable) and unblocking G3c-iii-b; §**1.12**
(2026-06-05, coordinator verification pass) is the **G3c-iii-b correctness gap**: the
composer `case_I_realization` (commit c1ef55a) carries a FALSE combinatorial equality
`hpinc` in its "Claim-6.4 bundle" (the contraction leg's complement-isolation is
generically unsatisfiable), making the theorem valid-but-vacuous — §1.12 diagnoses it,
**corrects the §1.9 premise**, and decides the fix (route (b)-corrected: an asymmetric
coupling that removes the contraction leg's rank-polynomial round-trip, so `hpinc`
never arises). The live to-do is the FIX (`notes/Phase22a.md` *Hand-off*). No Lean /
`\leanok` / blueprint edits accompany this doc.

Primary sources read for this pass: KT 2011 §5–§6.4 (`.refs/`, printed pp.
669–697); `Molecular/{AlgebraicInduction,Extensor,Deficiency,Induction}.lean`;
`blueprint/src/chapter/algebraic-induction.tex` Case I/II/III + `thm:theorem-55`;
`notes/Phase21b.md` *Finding A/B*; the cross-cutting `DESIGN.md` sections
(*Realization motive must be V(G)-relative*, *Constructibility recon …*,
*Phase Case-naming …*).

---

## 0. The crux, in one paragraph

KT Theorem 5.5 (printed p. 669) reads: *"there exists a **(nonparallel, if G is
simple)** panel-hinge realization `(G,p)` satisfying `rank R(G,p) =
D(|V|−1)−k`."* The induction is on `|V|`; **every inductive case invokes the IH
(KT's eq. (6.1)) in this same `∃ nonparallel realization` form** and builds a
new nonparallel realization from it. Three places consume the nonparallel-ness
of the *incoming* legs: (i) KT Claim 6.4's "each entry of the rigidity matrix of
a **nonparallel** realization is a polynomial in the panel coefficients"
(printed p. 674) — exactly the project's `panelRow`/B0 coordinatization, which
needs `supportExtensor e ≠ 0`, i.e. transversal hinges; (ii) Lemma 6.3/6.5's
boundary-panel intersection `Π_{G/E',p2}(u) ∩ Π_{G',p1}(v)` (eq. 6.6) is a
genuine `(d−2)`-flat **only when the two panels are transversal**; (iii) the
simple cases additionally require the two legs' panel coefficients to be
*jointly algebraically independent over ℚ* (printed pp. 673, 675), so they can
be placed on one shared generic point. The project's motive currently asks for a
**bare** rigid realization (`∃ Q, Q.graph = G ∧ Q rigid on V(G)`), with no
general-position promise. That mismatch **is** gap (G1); the joint-genericity in
(iii) **is** gap (G2). Both are intrinsic to KT's argument, not artefacts of the
Lean encoding.

---

## 1. Motive decision

### 1.1 What KT Theorem 5.5 actually guarantees

Settled what the strengthened motive must promise: KT's conclusion adds `Q.IsGeneralPosition` (pairwise normal independence) when `G` is simple, but GP genuinely fails at the parallel-K₂ double-edge base, so an *unconditional* GP motive is too strong — strengthen only conditioned on `G.Simple`. Durable: `HasFullRankRealization`/`IsGeneralPosition` defs; resolved via the two-motive split, §1.4.

### 1.2 What each producer NEEDS from / SUPPLIES to the motive

Settled that the green producer infra (`exists_rankPolynomial_of_rigidOn`, `hasFullRankRealization_of_splice_ofNormals`) *already* demands `hne`/`hgp` (transversality + general position) as hypotheses; the only gap is that the bare IH motive does not *carry* GP to discharge them — KT closes this by making the IH itself nonparallel. Durable: `notes/Phase22a.md`.

### 1.3 What breaks / must change if the motive is strengthened

Settled that the ripple cost of strengthening is bounded and front-loaded: the `HasFullRankRealization` def edit + transitive `theorem_55` re-type + base-case GP conclusion is one small commit; the device feed lemmas already take `hne`/`hgp` so they get *easier* to feed, not broken; the one genuine new burden is handling the non-general-position parallel-K₂ base. Durable: `notes/Phase22a.md`.

### 1.4 Recommendation

Decided: strengthen the motive but condition GP on `G.Simple`, via the **two-motive split** (separate `HasGenericFullRankRealization` carried through simple cases + a one-line forgetful map to bare `HasFullRankRealization`) as the lower-ripple option that touches no Phase-20 node. Durable: `HasGenericFullRankRealization`, `hasFullRankRealization_of_generic`; `notes/Phase22a.md`.

### 1.5 Generic-motive recon — the route is a hybrid (2026-06-04)

Settled the N6-composer IH-shape gap as a **hybrid** (Route 2 *and* Route 1, not alternatives): N6-G1 makes the producer generic (`hasGenericFullRankRealization_of_splice_ofNormals`, GREEN — realizes at the GP seed `q₀` directly, bypassing the device after the spike found the device-output-is-GP premise false), then N6-G2 makes the IH generic via the conditioned reduction. Durable: `notes/Phase22a.md`.

### 1.6 N6-G2 re-recon — the generic-motive reduction, decomposed (2026-06-04)

Decided: condition the motive on `G.Simple` (form (A) `Pc`) and route `Simple`-failure cases to the bare conjunct (no unconditional GP). Cut into G2a (`theorem_55_generic`, the reduction skeleton; flagged `hsplit` sub-question resolved by *scope* — it is Case III, out of 22a) / G2b (`map_simple`+`rigidContract_simple`, the new `map`/`collapseTo` simplicity fact) / G2c (wire into the simple-Case-I `hcontract`). All GREEN. Durable: `notes/Phase22a.md`.

### 1.7 N6-G3 re-recon — the `Gc ≤ G` mismatch is KT's Claim 6.4 transport; the splice's contraction leg is `G ＼ E(H)`, not the relabelled `rigidContract` (2026-06-05)

Settled the `Gc ≤ G` mismatch: it dissolves at the graph level (the splice's contraction leg is `G ＼ E(H)` ≤ G, per KT eq. (6.3), not the relabelled `rigidContract`) but relocates to the placement level as the genuinely-new KT Claim 6.4 transport. Cut into G3a (`rigidContract_rigidity_transport`, GREEN-MODULO — carries Claim 6.4 as explicit `htransport`) / G3b (`couple_geometry_…`) / G3c (assembly). Durable: `notes/Phase22a.md`.

### 1.8 G3c re-recon — the splice coupling hardcodes each leg rigid on its *full* `V(·)`, but the contraction leg is rigid only on `V∖V′ ∪ {v∗}`; G3c is NOT pure green-brick assembly (2026-06-05)

Found that G3c is not pure green-brick assembly: every Case-I coupling/producer above the base glue hardcodes each leg rigid on its *full* vertex set, but the contraction leg is rigid only on `sc = (V(G)∖V(H)) ∪ {r}` — a body-set mismatch. Forced building body-set variants of the splice/coupling bricks. Durable: `notes/Phase22a.md`; G3c-i body-set producer bricks.

### 1.9 G3c-ii re-recon — the body-set N3 consumer needs the complement-isolation equality; route (a) (carry it as `h…`), buildable, mirrors `isInfinitesimallyRigidOn_vertexSet_of_finrank_le` (2026-06-05)

Decided route (a): carry the body-set complement-isolation equality `hpin` as a hypothesis to the body-set N3 consumer / coupling. **PARTLY WRONG, corrected in §1.12:** the `sH := V(H)` half is honest (green `finrank_pinnedMotionsOn_vertexSet`), but the contraction-leg `hpinc` on `sc` is generically *unsatisfiable* (interior bodies are not isolated), making `case_I_realization` valid-but-vacuous. Durable: §1.12; `notes/Phase22a.md`.

### 1.10 G3c-iii re-recon — the GP conjunct needs a body-set *generic* coupling (built); the residual assembly faces the parent-`ends` impedance + Claim-6.4 bundling, not pure green-brick assembly (2026-06-05)

Landed the two body-set *generic* producer bricks (`hasGenericFullRankRealization_of_splice_set_ofNormals`, `…_couple_ofNormals_set`) and re-cut the residual assembly into G3c-iii-a (the parent-`ends` impedance recon) + G3c-iii-b (composer assembly + flip), having found two unsurfaced obstructions (the `ends` impedance + Claim-6.4 bundling). Durable: `notes/Phase22a.md`.

### 1.11 G3c-iii-a re-recon — the parent-`ends` impedance dissolves: the producers need only an *edge-restricted* `hends`, which is constructible from `G` alone; resolution is option (iii), verified buildable (2026-06-05)

Settled the parent-`ends` impedance as option (iii): the producers never need the all-`β` `hends`, only an *edge-restricted* form, which is constructible from `G` alone via a small `exists_ends_of_graph`-style side-lemma; relax the body-set couplings' `hends` to match. Not a layer-wide motive re-typing. Durable: `notes/Phase22a.md`; the `> §1.9 premise CORRECTED — see §1.12` box below stands.

### 1.12 G3c-iii-b correctness gap — the contraction leg's complement-isolation `hpinc` is a FALSE combinatorial equality, not Claim 6.4; the round-trip itself must be removed for that leg (2026-06-05, coordinator verification pass)

Diagnosed the §1.9 correctness gap: `hpinc` is a placement-independent (`∀ q`) combinatorial dimension equality, NOT Claim 6.4, and is generically false (witness at D≥3). Decided **route (b)-corrected**: an asymmetric coupling (`hasGenericFullRankRealization_of_couple_asymm_ofNormals_set`) runs only the `H`-leg through the rank-poly round-trip and feeds the contraction leg's rigidity directly from `htransportGP`, deleting `hpinc`. (Fix landed; then superseded by §1.13's re-architect.) Durable: §1.13; `notes/Phase22a.md`.

### 1.13 Second coordinator verification — the §1.12 asymmetric fix is ALSO undischargeable; the real divergence is motion-space glue vs KT block-triangular; re-architect (2026-06-05)

Found the §1.12 asymmetric `htransportGP` *also* undischargeable (it needs the false "GP ⟹ rigid"); the root cause is that Phase 21b translated KT's block-triangular rank-addition (eq. 6.3) into the project's common-seed motion-space splice glue, which demands a single shared placement KT never needs. **Owner-directed decision: re-architect Case I to KT's block-triangular form.** Durable: §1.14; `DESIGN.md` *Match the source's argument structure …*; `notes/Phase22a.md`.

### 1.14 Block-triangular reframing — design (Stage 2, verified; pending owner sign-off to implement) (2026-06-05)

Designed the block-triangular reframe: replace the common-seed splice with KT eq. (6.3) rank-addition routed through the device's independent-row counting, with Piece B (union-independence of `s_H ⊔ s_c` via the **exterior**-column projection `extProj H`, ~40–60 lines, scratch-verified) the block-triangular core, leaving a single honest green-modulo residual `hsc_proj_indep` (exterior-projected surviving-row independence = KT Claim 6.4 eq. 6.5/6.9). Durable: §1.16; `notes/Phase22b.md`.

### 1.15 Stage 3 — molecular 17–22 KT-divergence audit (clean; reframe corroborated) (2026-06-05)

Audited molecular phases 17–22 for sibling structural divergences. **Result: the Case-I splice (§1.13) is the only one; no new blocker.** Cases II/III are SAFE (they already use KT's block-triangular column split `linearIndependent_sum_pinned_block`, N7b-3), corroborating the §1.14 reframe; clean bills for 17/19/20/21/21a. Forward flags: 22b's residual must be `hsc_proj_indep`, not `htransportGP`; verify Phase-21a `complementIso` sign before Phase 25. Durable: `notes/Phase22b.md`, `notes/Phase21a.md`.

### 1.16 The §1.14/Stage-4 residual was over-quantified (∀-GP); the dischargeable form is Qc-non-root (verified) (2026-06-05)

Corrected the Stage-4 residual: `∀ q, GP(q) → …` is the same over-quantification as `htransportGP` (needs the false "GP ⟹ max rank"). The dischargeable form conditions on a surviving rank polynomial `Qc`-non-root threaded into the seed via `QH · Qc · Qgp`, which reduces exactly to KT eq. (6.9). Meta-lesson (promoted to `DESIGN.md`): condition `∀`-genericity residuals on the specific Zariski-open locus, not on every GP placement. Durable: `notes/Phase22b.md`.

### 1.17 N-22b-1 re-recon — the rank-transport reduces to a single-placement exterior-projected surviving-row witness; the analytic core is `htransport` (KT eq. 6.9), the brick is plumbing (2026-06-05)

Decided N-22b-1 = `rigidContract_exterior_rank_transport` carrying the single-placement exterior-projected surviving-row witness as explicit `htransport` (KT eq. 6.9), with N-22b-2/3 as plumbing; the analytic core admits no green-brick reduction (the collapse-normal mismatch). **[Irreducibility softened by §1.18: `htransport` decomposes into a 5-node plan reusing the genericity engine.]** Durable: `rigidContract_exterior_rank_transport`; §1.18; `notes/Phase22b.md`.

### 1.18 Validation of the `htransport` deferral + the discharge plan (5-node cut; stays Phase 22b, paused) (2026-06-05)

Validated the `htransport` deferral (correct — does not fit a few-commit finish) but softened §1.17's irreducibility: the discharge is a concrete 5-node cut (T1→T2a→T2b→T3→T4) reusing the existing genericity engine, with T2b (lower-semicontinuity) the analytic crux. 22b stays open and **paused** at the reduction checkpoint, resume gated on a T2b re-recon. Durable: §1.19; `notes/Phase22b.md`.

### 1.19 T2b math-first re-recon — the lower-semicontinuity step is already green inside N-22b-2; the walling node is the collapse-relabel row reproduction (was T2a), and the cut shrinks 5→4 nodes (2026-06-05)

Found T2b dissolves (the lower-semicontinuity lift is already green/wired in N-22b-2; the witness can be the degenerate member `q₀^deg` directly, no generic placement needed). Re-cut to 4 nodes (U1→U2→U3→U4) with U2 (collapse-relabel projected-row reproduction) the walling crux. **[Corrected by §1.20: the crux did not vanish, it moved from U2 to U3.]** Durable: §1.20; `notes/Phase22b.md`.

### 1.20 The U2 build surfaced the real crux: U3 is NOT plumbing — the exterior-projection drops the `r`-column, so it needs a pin-a-body rank-preservation brick (the genuine KT Claim 6.4) (2026-06-05)

Found U3 is not plumbing: `(extProj V(H)).dualMap` drops the `r`-column, and that this preserves rank `D(|sc|−1)` IS the genuine KT Claim 6.4 (a pin-a-body fact, no green brick). Split U3 into U3a (alignment transport, O1, bricked) + U3b (the pin-the-`r`-column projected-rank crux, missing infra). U1/U2 landed sound. Durable: §1.21; `notes/Phase22b.md`.

### 1.21 U3b recon — the crux is bounded: `(extProj V(H)).dualMap` on the contracted framework = pin-at-`r`, so U3b is the projected sibling of the green U3 tool off Lemma 5.1, not a from-scratch research lemma (2026-06-05)

Recon claimed U3b is one bounded brick: `extProj V(H)` on the contracted `Qcf'` = pin-at-`r`, so rigidity on `sc` gives `finrank Z = D` ⟹ `finrank(pinnedMotions r) = 0` ⟹ projection loses zero rank (Lemma 5.1). **[Corrected by §1.22: `finrank Z = D` is FALSE for `sc ≠ α` — it is `D·(|scᶜ|+1)`; the clean conclusion survives only via an exact free-isolated-body cancellation.]** Durable: §1.22; `notes/Phase22b.md`.

### 1.22 U3b build-recon — the recon's "finrank Z = D" is false for `sc ≠ α`; the brick closes via `Z ⊔ range(extProj V(H)) = ⊤`, whose real content is the rigid-block pin-count `finrank(pinnedMotionsOn_F V(H)) = D(|scᶜ|−|V(H)|+1)` (2026-06-05)

Corrected the U3b layer and BUILT it: the brick reduces to `Φ ⊓ ker D = ⊥` ⟺ `Z ⊔ range(extProj V(H)) = ⊤`, whose real content is the rigid-block pin-count. Landed `finrank_pinnedMotionsOn_of_isInfinitesimallyRigidOn_vertexSet_inter_eq_singleton` (the pin-count walling node), `infinitesimalMotions_sup_range_extProj_eq_top`, and `exists_independent_panelRow_subfamily_of_rigidOn_linking_set_proj` (via `injOn_extProj_dualMap_rigidityRows` + `map_injOn`) — all U3b sub-bricks, axiom-clean. Durable: `notes/Phase22b.md`.

### 1.23 U3a build-recon — the §1.20 "alignment RESOLVED in principle" is NOT buildable as scoped: the IH motive `HasGenericFullRankRealization` carries an *arbitrary* `ends` (no link-recording), so `Q`'s rigidity does not transport to the `endsᵐ` selector; the same gap is already an *undischarged* `hbundle` conjunct for the `H`-leg (2026-06-05)

Found U3a not buildable as scoped: the IH motive carries an *arbitrary* `Q.ends` with no link-recording, so the `ends`-swap transport fails — the same gap is already an undischarged `hswap` conjunct for the `H`-leg. The honest fix is a motive strengthening (add the link-recording conjunct), a Phase-21/22-touching structural edit, not a leaf build. Lesson lifted to `DESIGN.md` (*A realization motive must carry the selector invariants its consumers read*). Durable: §1.24; `notes/Phase22b.md`.

### 1.24 Route-(i) scope verification + the U3a/U4 commit sequence — the motive strengthening is *generic-motive only*, all producers supply link-recording from `endsOf`, the three risk items confirmed (with two refinements) (2026-06-05)

Verified route (i) (strengthen the motive with link-recording) buildable: scope is generic-motive-only (`HasGenericFullRankRealization`), every producer supplies link-recording for free (fresh `ofNormals G ends q₀`, composer manufactures `G.endsOf`), and the three risk items hold — (a) edge-restrict `hne_ends`, (b)'s bridge `endsOf_eq_or_swap` already landed, (c) one small `IsLink.map`-under-`collapseTo` lemma. Gave the 5-commit sequence ending in the `lem:claim-6-4` flip + phase-close. Durable: `notes/Phase22b.md`.

---

### 1.25 Phase 22c opens — Case III at `d=3` (KT Lemma 6.10), first layer recon (2026-06-05)

22b closed (Claim 6.4 green). Phase 22c opens Case III at `d=3` / Track B — the `theorem_55.hsplit` branch at `k=0`, the conjecture's crux (KT §6.4.1, ~12 pages) — design-pass-first (layer recon, not build). First pass read Lemma 6.10 against the primary source (pdf pp. 34–45): the eq. (6.12) degenerate placement `p₁(vb)=q(ab)` reproduces the `e₀=ab`-row, block-triangular with `R(G_v^{ab},q)` ⟹ `rank ≥ D(|V|−1)−1`, one short; the `D`-candidate argument (Claim 6.11 redundant-row + Claim 6.12 extensor-span on green Lemma 2.1) supplies the missing row. Scope cut: 22c = Case III at `d=3`, the `d=3` assembly deferred. Durable: `notes/Phase22c.md` *First design-recon pass*; four open questions → §1.26.

### 1.26 Phase 22c, second pass — the four questions + the three-strata scope cut (2026-06-05)

Resolved the four open recon questions: (Q1) candidate normal form — state ONE per-candidate row-op lemma, instantiate ×3 (`p₁`/`p₂` symmetric `a↔b`, `p₃=p₁∘ρ`); (Q2) `d=3`-first YES (KT's own §6.4.1-then-§6.4.2 cut; general `d` → Phase 23); (Q3) Claim 6.11's row-matroid bridge = Lemma 4.3(ii)+IH, the genuinely-new redundant-row crux; (Q4) Claim 6.12's "same `r`" IS eq. (6.44) (degree-2 forcing), folds into the contradiction on green Lemma 2.1 — not a separate brick. Partitioned Lemma 6.10 into three difficulty strata — (1) eq. (6.12) `+(D−1)` placement [buildable, green N7b infra]; (2) Claim 6.11 redundant row [research crux]; (3) Claim 6.12 + candidate normal form [assembly] — and cut **22c = stratum 1**, strata 2–3 to later sub-phases (defer-the-finer-cut). Durable: `notes/Phase22c.md`.

### 1.27 Phase 22c, third pass — blueprint reconciliation to the eq. (6.12) row-side route (2026-06-05)

Found a build-blocker: the live blueprint prose for the exact nodes 22c builds (`lem:case-II-realization`, `lem:case-II-realization-placement`) was self-inconsistent — statements said the motion-side M3 / row-side N7b-4 "superseded" while their proofs still routed through them. Reconciled both to the eq. (6.12) row-side degenerate placement; retain-with-marker struck M1/M2/M3 + N7b-4 (no live dependency edge). Confirmed 22b's `degeneratePlacement`/`extProj` block-collapse is NOT reused (stratum 1 is single-vertex; block-triangularity from the pin-a-body split N7b-3, not projection). The calibration case behind the supersession gate. Durable: `notes/Phase22c.md`; `blueprint/CLAUDE.md` *supersession gate*.

### 1.28 Phase 22c, fourth pass — signature-level verification of the stratum-1 cut (2026-06-05)

Signature-level constructibility recon of the one new brick (`p₁`+`hrow`) against the five green bricks' actual signatures (N7b-0/1/2/3 + N7a form (b)) — composition verifies clean, no mismatch. Load-bearing structural fact: `panelRow (ofNormals G ends q)` reads only `ends`+`q`, NOT `G` (`toBodyHinge_supportExtensor` `rfl`), so N7b-2's old-block `hrow` is `rfl` on `ends`/`q` agreement. Corrected a `notes/Phase22c.md` *Hand-off* conflation: the eq. (6.12) `p₁(vb)=q(ab)` reproduction is the NEW-block content (feeds `hnewpin`/N7b-3), not N7b-2's `hrow`. Count `(D−1)+D(|V|−2)=D(|V|−1)−1` closes — a lower-bound brick, explicitly NOT `HasFullRankRealization`. Durable: `notes/Phase22c.md`.

### 1.29 Phase 22c, fifth pass — single-seed coupling + placement geometry (2026-06-05)

Resolved the piece §1.28 left at requirements level (the shared-seed selector geometry). (A) Single-seed coupling SOUND: `q₀ := Function.update q v (n_a+t·n_b)` leaves the old block untouched (IH rigidity quantifies over `V(G_v^{ab})=V∖{v}`, motions avoid `v`; lever `toBodyHinge_withNormal_infinitesimalMotions_eq`). (B) Placement `q₀(v,·):=n_a+t·n_b`, `t≠0`: reproduces the `ab`-row (`n_b∧n_b=0`) AND keeps the `va`-hinge a nondegenerate line `L⊂Π(a)` — the `t=0` trap zeros `va`; use `t≠0` for KT fidelity. (C) Sub-lemma cut bounded; `hnewpin` landed as `linearIndependent_panelRow_comp_single_of_edge`. PLAN CLEAR. Durable: `notes/Phase22c.md` (producer `case_II_placement_eq612`).

### 1.30 Phase 22d, footnote-6 kernel recon — the new content is a `non-root-from-algebraic-independence` brick (2026-06-06)

"Size the kernel" re-test of the Gap-3 verdict against current signatures. Confirmed two structural claims — (a) the matroid↔row link IS `rigidityMatrix_prop11` (the IH, not a separate iso), (b) redundancy-from-count is pure LA pigeonhole — but **refuted** (c) "eq. (6.22) re-exposes from the device": the 22b motive is still `∃Q` existence + degree-1 GP, NOT rank-poly non-root-ness, and the project has ZERO `AlgebraicIndependent` machinery. Named the genuinely-new content: a `non-root-from-alg-independence` brick = (i) an `eval_ne_zero_of_algebraicIndependent` mirror + (ii) a seed-alg-indep motive invariant. Durable: `notes/Phase22d.md` *Footnote-6 kernel recon*; `notes/AlgebraicIndependence.md`.

### 1.31 Phase 22d, kernel-route decision + the alg-independence relaxation tracker (2026-06-06)

§1.30 named the kernel (default: carry-as-hypothesis). **User decision: build the algebraic-independence route DIRECTLY to green** (KT's actual argument) — not carry-as-hypothesis, not the unverified product-route shortcut. The product-route (choose the seed as a non-root of the finite product of nested-IH rank polynomials, avoiding alg-indep at `d=3`) → deferred relaxation TODO, with every alg-indep site tracked in the standing note **`notes/AlgebraicIndependence.md`** (the single source). Durable: `notes/Phase22d.md` *Kernel-route decision*; `notes/AlgebraicIndependence.md`.

### 1.32 Phase 22d, kernel sub-phase (ii) opening recon — (ii) SPLITS into a motive conjunct + a rationality bridge (2026-06-06)

Math-first recon at the (ii) node's open. Found (ii) is NOT a single leaf and NOT pure motive-strengthening — it SPLITS: **(ii-a)** the seed-genericity motive conjunct [22b-shaped plumbing; producers build at an alg-indep seed — moment-curve candidate, confirm alg-indep over ℚ] + **(ii-b)** a rationality bridge [NEW, the §1.30 cut missed it]: leaf (i) needs the rank poly over ℚ but the device's `Q` is ℝ-typed (`complementIso`-`repr` constants, rational but not manifestly so), so it needs a descent `eval q Q = aeval q Q₀` via `MvPolynomial.map (algebraMap ℚ ℝ)` — zero such scaffolding in the tree. (b2) post-hoc coefficient-rational descent is the lighter cut (recommended); (b1) re-type the whole coordinate chain is the fallback. Durable: `notes/Phase22d.md` *Kernel sub-phase (ii) recon*; `notes/AlgebraicIndependence.md` row #105.

### 1.33 The `d=3`-assembly opening recon + the Phase-23 general-`d` reuse map (2026-06-07)

**(A)/(B) recon arc — verdict landed, canonical home is `notes/Phase22g.md`.** The `d=3`-assembly
obligation re-scoped to one real gap (the `d=3` `hsplit` producer; `hub` green, `theorem_55` a
green conditional); the two open items resolved at Phase-22g open — **(B.1)** the `hsplit`/
`theorem_55` path does NOT consume `lem:cycle-realization` (KT Lemma 5.4 is a KT-narrative, not
Lean-load-bearing, dependency; reconciled in the blueprint), **(B.2)** add a small `d=3`-instance
`theorem_55` node. Full verdict + the build spine: `notes/Phase22g.md` *Red-node consistency gate*
+ *Current state*. (C)/(D)/(E) below stay live as Phase-23 design support.

#### (C) KT §6.4.2 (Lemma 6.13) reuse map — what general `d` reuses, replaces, adds

KT, p. 692: *"The proof strategy is exactly the same as `d = 3`."* General `d` runs a length-`d`
chain `v₀…v_d` with `d` candidate frameworks `(G,p_i)` and isomorphisms `ρ_i` (eq. 6.54).

| Ingredient | Status for Phase 23 | Note |
|---|---|---|
| **Claim 6.11** (redundant `ab`-row), `exists_redundant_panelRow_ab_of_finrank_eq` | **reused verbatim, already general & GREEN** | p. 693 "redundant edge always exists by Claim 6.11"; the single hardest combinatorial piece — done |
| **Lemma 2.1** (extensor independence), `omitTwoExtensor_linearIndependent` | **reused verbatim, general & GREEN** | p. 698 "= `(d+1 choose d−1) = D` by Lemma 2.1"; only the `span_omitTwoExtensor_eq_top` *corollary* is `d=3`-stated (Fin 4 / `ScrewSpace 2`) — re-state at general grade |
| `complementIso`, `complementIso_toDual`, step-(i)/(ii) generality lemmas, `topEquiv`/`pairingDualEquiv` mirrors | **general & GREEN** | dimension-parametric already |
| genericity device, `prop:rigidity-matrix-prop11`, `theorem_55` skeleton, Cases I & II | **general & GREEN** (Case I) | the spine is `k`-free |
| Candidate count + chain bookkeeping (eqs. 6.46–6.64) | **NEW** — `3` candidates → `d` along a chain; isos `ρ_i` | index-heavy but mechanical; the **graph-free** `linearIndependent_sum_augment_candidateRow` is reusable, so it's plumbing not research |
| The **duality** (N3b analog) | **REPLACE** — `⋀²ℝ⁴` → **`⋀^{d−1}ℝ^{d+1}`** | a `(d−1)`-extensor ↔ panel-meet `C(L_i)`; the bespoke `⋀²ℝ⁴` count is `d=3`-only |
| "same `r`" reduction | NEW but direct — eq. (6.44) → eq. (6.66) ("±`r`" chain) | the N8 `candidateRow_ac_eq_neg` analog along the chain |
| Affinely-independent points (N3a analog) | **NEW** — `d+1` points, `j` hyperplanes meet in `(d−j)`-flats | KT uses **algebraic independence** here (p. 698); the hammer **already exists** (built 22d) |
| **Lemma 4.6** (chain-or-cycle dichotomy) + **Lemma 4.8** (split-off along chain minimal 0-dof) | check Phase-20 status (no explicit node found; may be subsumed in `minimal_kdof_reduction`) | needed to enter the chain case |
| **Lemma 5.4** (cycle base, length ≤ `d`) | the deferred sub-phase (risk #4); see (B.1) | genuinely needed at general `d` for the short-cycle base, even if `d=3` dodges it |

#### (D) Grassmann–Cayley / exterior-duality API extent — build it LAZILY in Phase 23

User's instinct (build the API at need, not speculatively) is correct, with one nuance:

- **Do NOT build a general Hodge-star / regressive-product / star-operator API.** KT never needs
  it. The whole duality is *"the join of `d−1` points spanning a `(d−2)`-flat = the meet of the
  panels containing it, as the same Plücker line."* That is the **top-power-is-1-dimensional**
  fact (`⋀^n W` is 1-dim when `dim W = n`), not a star operator.
- **The bespoke `⋀²ℝ⁴` count is `d=3`-only; do not generalize it.** The landed N3b proof routed
  via `Ω = dim 6 − 5` using `wedgeFixedLeft` / `inf_range_wedgeFixedLeft` / the `5 = 3+3−1`
  inclusion–exclusion. That route does not generalize.
- **The clean general route's infra is ALREADY PARTLY LANDED (the happy accident).** 22f also
  built `extensor_mem_range_map_subtype_of_mem` + `exists_smul_eq_of_mem_range_map_subtype`
  (place both members in `range(exteriorPower.map (d−1) W.subtype)`, which is 1-dim) and then
  *didn't use them*. That "unused" route is the one that generalizes — it rests on
  `exteriorPower.finrank_eq`, `exteriorPower.map_injective_field`, `map_apply_ιMulti` (all
  mathlib) + the project's `topEquiv`/`pairingDualEquiv` mirrors. So the general duality needs
  **modest, mostly-mathlib API**, deferred to Phase 23 where the grade is concrete.
- **Alg-independence for the general-position points: the hammer already exists** (22d, for the
  Claim-6.11 seed kernel), so the general-`d` N3a analog is "apply existing machinery," not
  "build new." Re-examine `AlgebraicIndependence.md` risk (c) then (does the touched-subgraph
  family grow with `d`?). Add the general-`d` site as a tracker row when Phase 23 opens.

#### (E) Recommended sequence

1. **Next sub-phase (unlettered → minted on open): the `d=3` assembly.** Open on a build-free
   red-node consistency recon resolving (B.1)–(B.2). Then build the `d=3` `hsplit` producer
   (the spine in (A)), instantiate `theorem_55 (n:=2)`, feed `rigidityMatrix_prop11`'s `hgen`,
   do the Thm 5.5→5.6 push. Milestone: the molecular conjecture proved at `d=3`, unblocking
   Cor 5.7. Phases 24–25 (`d=3` bar-joint matroid, projective duality) can proceed in parallel —
   they don't gate on the rank theorem until Cor 5.7 (Phase 26).
2. **Phase 23 (general `d`, Lemma 6.13).** Scope with the (C) reuse map: reuse Claim 6.11 +
   Lemma 2.1 verbatim; generalize the candidate chain on the graph-free assembly; build the
   `⋀^{d−1}` duality via the top-power route ((D), the already-landed `map`-range infra);
   apply the existing alg-independence machinery for the points; reuse the `d=3` assembly as
   the template. Open with its own recon (read eqs. 6.46–6.67 against the `d=3` Lean) and add
   the general-`d` alg-independence row to `AlgebraicIndependence.md`.

---

### 1.34 The `d=3` `hsplit` producer core — cracked into named leaves (2026-06-07)

**Decision: green-modulo-skeleton-first (§1 question 1 = YES).** State the `hsplit` producer with
its residual graph-data obligations as EXPLICIT hypotheses, flip the SKELETON green first, then
discharge each as its own leaf. This forces the spine to land, converts the "multi-session blob"
into named leaves, and — critically — **isolates the §38 defeq trap into one leaf (L3)** so the rest
of the spine builds graph-free over already-green bricks. The decomposition reads the actual Lean:
`case_II_placement_eq612` (CaseI.lean:2617, the eq.-(6.12) `+(D−1)` block at real graph data, GREEN),
the candidate producers (`linearIndependent_sum_p2/p3_candidateRow` + the assembly
`linearIndependent_sum_augment_candidateRow`, RigidityMatrix.lean, GREEN, graph-free), the selection
capstone `case_III_eq629_conditional` (GREEN), and the packaging feed
`hasFullRankRealization_of_independent_panelRow_index` (GenericityDevice.lean, GREEN).

**Three load-bearing structural facts the recon established** (each de-risks a leaf):

- **(F1) The candidate row IS a `panelRow`.** `panelRow ends (e, t₁, t₂)
  = hingeRow (ends e).1 (ends e).2 (annihRow (C(e)) t₁ t₂)` (`Pinning.lean:46`, `def panelRow`). So
  the candidate row `hingeRow v a ρ` consumed by `linearIndependent_sum_augment_candidateRow` is
  literally `panelRow ends (e_a, t₁, t₂)` once `ρ := annihRow (C(e_a)) t₁ t₂` and `ends e_a = (v,a)`.
  This is what lets the `+1` candidate summand be placed at an `(edge, ⋀ᵏ-pair)` by the index map `j`
  (§2 below) — no laundering: the candidate row is a genuine rigidity row of the candidate placement.
- **(F2) `splitOff ⊀ G`, but `case_II_placement_eq612` already only needs `Gv ≤ G` for ONE step.**
  Its `hGv : Gv ≤ G` is used solely for the rigidityRows-*membership* step (CaseI.lean:2802,
  `IsSubgraph.isLink_iff`); the old-block independence + transport run through `f := id`, `hrow :=
  rfl` over the COMMON SUBGRAPH `G − v` (`exists_independent_panelRow_transport`, GenericityDevice.lean:399 —
  graph-free, `panelRow` reads only `ends`/`q`). So the candidate path reuses N7b-2 VERBATIM; what is
  new is supplying the membership for the candidate row's edge `e_a` (which DOES link `v a` in `G`,
  `hG_ea`) — see L4. (§3 below.)
- **(F3) The candidate producers need the FULL hinge-row block, not just an independent subfamily.**
  `linearIndependent_sum_p2/p3_candidateRow` take `rn` with BOTH `hrnpin` (pinned independence) and
  `hspan` (pinned span `= F.hingeRowBlock e`). `case_II_placement_eq612`'s new block came from
  `exists_independent_panelRow_subfamily_of_edge` (an independent `D−1` subfamily — gives `hrnpin` via
  `linearIndependent_panelRow_comp_single_of_edge`, but NOT the span equality). The span half is
  `span_panelRow_edge_eq` + `finrank_hingeRowBlock` (both GREEN, Pinning.lean) packaged as a small
  bridge leaf (L2). The assembly route `linearIndependent_sum_augment_candidateRow` (used for the
  `M₁`/`p₁` candidate) needs only `hnewpinaug`, which `linearIndependent_sumElim_candidateRow_iff`
  supplies from `hrnpin`+`hspan`+`hsel` — same inputs.

**The leaf sequence (bottom-up, each a smallest-buildable commit):**

- **L0 — `hsplit` skeleton (green-modulo, the spine).** State
  `case_III_hsplit_producer` (CaseI.lean) over the `theorem_55.hsplit` premise data
  (`G v a b eₐ e_b e₀`, the links, degree-2 closure, `e₀ ∉ E(G)`) plus
  `HasFullRankRealization k (G.splitOff v a b e₀)`, carrying as EXPLICIT `h…` hypotheses: the three
  candidate families + their `hselᵢ` (the row-space-criterion conditions `r̂(Cᵢ) ≠ 0 →`), the affine-
  independence + N3b-duality at the real candidate data (`hp`/`hduality`/`hr` of
  `case_III_eq629_conditional`), and the `j`-packaging (L5). Body: extract the IH `ofNormals` rigid
  locus (`exists_rigidOn_ofNormals_of_hasFullRankRealization`), run `case_II_placement_eq612` for the
  `D(|V|−1)−1` old+new blocks, select the winning candidate via `case_III_eq629_conditional`, feed
  `hasFullRankRealization_of_independent_panelRow_index`. **Smallest first leaf** — flips the producer
  green-modulo and names L1–L5. Defeats the blob.
- **L1 — IH → candidate `rn`/`ro`/`ρ` extraction.** From the IH-extracted rigid `ofNormals (splitOff)
  ends q` (the `Gv := splitOff` block, rigid on `V(splitOff) = V(G)∖{v}`), produce the old block `ro`
  (N7b-0 `exists_independent_panelRow_subfamily_of_rigidOn_linking`, exactly as
  `case_II_placement_eq612` does) and the new block `rn` (one of `v`'s edges). Mostly a re-slice of
  `case_II_placement_eq612`'s internals; graph-free over `ofNormals`. Shape: produces the `ιn`/`ιo`
  families + `hold`/`holdindep` the assembly consumes.
- **L2 — the pinned-block span bridge (F3). LANDED** (`span_panelRow_comp_single_of_edge`,
  Pinning.lean). `rn` pinned through `v`'s column spans `F.hingeRowBlock e_b`: each pinned row IS the
  bare `annihRow (C(e)) t₁ t₂ ∈ r(p(e))` (`single v` reads `v`, the distinct other endpoint `0`), `=`
  by equal `finrank D−1` (`linearIndependent_panelRow_comp_single_of_edge` + `finrank_hingeRowBlock`).
  The `comp Φ` the producers carry is identity at the pin (`columnOp hvb (single v x) = single v x`,
  `b ≠ v`), so this `hspan` feeds them directly. A small `Submodule.eq_of_le_of_finrank_eq` leaf,
  mirroring `exists_redundant_panelRow_of_edge_of_finrank_lt`'s `hrspan`.
- **L3 — the §38 defeq leaf, ISOLATED.** The one place real graph data meets the `ofNormals`/`withGraph`
  `whnf`/`isDefEq` trap: showing the seed `q₀`/selector `ends` of the candidate placement gives the
  candidate row's supporting extensor `C(e_a) ≠ 0` (the `va`-line `L ⊂ Π(a)`, KT eq. (6.12), `t ≠ 0`)
  AND that the `rn`-block is at the SAME framework as the assembly's `Sum.elim` output. `case_II_placement_eq612`
  already discharges the `hane`/`hnewne` extensor-nonzero facts (CaseI.lean:2713/2721) — REUSE those;
  the residual is aligning the candidate placement's framework with the assembly. **Decide PROACTIVELY
  (§1 question 4): route through `…_index` WITHOUT a bespoke helper if the families are built directly
  as `panelRow (ofNormals G ends q₀)` subfamilies (then `j` is identity-on-edge-index and the framework
  is syntactically one term).** Extract a generic helper (`mem_infinitesimalMotions` round-trip per §38)
  ONLY if a single `convert`/`rw` `whnf`-walls — name it `panelRow_ofNormals_candidate_eq` (the
  `panelRow`-reads-only-`ends`/`q` `rfl`, à la `toBodyHinge_supportExtensor`). L0's green-modulo state
  lets L3 wall in isolation without re-walling the spine.
- **L4 — candidate-row membership.** The candidate row's edge `e_a` links `v a` in `G` (`hG_ea`,
  premise data), so `panelRow_mem_rigidityRows` gives the rigidityRows membership for the `+1` summand
  — the analog of `case_II_placement_eq612`'s membership step (CaseI.lean:2795), now for `e_a` instead
  of via `hGv`. Closes the F2 gap.
- **L5 — the `j` / `Sum.elim` packaging (§1 question 2).** See §2 below; `j`'s injectivity is its own
  leaf — YES, the candidate analog of `case_II_placement_eq612`'s `hjinj` (one extra `Unit` summand).
  **Split when built: L5-inj LANDED** (`candidateCompletion_index_injective`, CaseI.lean — abstract over
  the three disjointness facts; note it needs a NEW `hso_ne_ea` fact L1 doesn't yet emit, since `so`
  must avoid `e_a` too, both linking the fresh `v ∉ V(Gᵥ)`). **L5-pack remains** = the `panelRow ∘ j`
  family identity + count. **(F1) subtlety surfaced building L5:** the candidate producer's `ρ` is a
  *general* block functional in `r(p(e_a)) = (span C)^⊥`, NOT a priori a single `annihRow (C) ta tb`, so
  the `Unit`-summand `hingeRow v a ρ` is not literally one `panelRow` (F1 as stated needs `ρ` to be a
  single `annihRow`). L5-pack resolves this: either realize `ρ` as a specific pair via
  `span_annihRow_eq_dualAnnihilator` (the block IS spanned by the `annihRow` family) and pick the
  candidate row from such a pair, or restate the device feed (`…_index`) to accept a `Sum.elim` of
  `panelRow`s + one block functional directly. Assess the smaller commit when L5-pack opens.

#### §1 question 2 — the `j` / `Sum.elim` packaging bridge (concrete)

The candidate-completion output (`linearIndependent_sum_augment_candidateRow`) is indexed by
`ι := (ιn ⊕ Unit) ⊕ ιo` — the `Sum.elim (Sum.elim rn {candidate row}) ro` shape. The injective
`j : ι → β × ⋀ᵏ-pair × ⋀ᵏ-pair` placing each summand at its `(edge, ⋀ᵏ-pair)`:

- `ιn`-summands (the new-block rows `rn`) → their existing `(e_b, t₁, t₂)` indices (`rn` came from
  `exists_independent_panelRow_subfamily_of_edge` on edge `e_b`, so each carries a `(e_b, ·)` index).
- the `Unit`-summand (the candidate row `hingeRow v a ρ`) → `(e_a, t₁, t₂)` where `ρ = annihRow (C(e_a))
  t₁ t₂` (F1); pick the `(t₁,t₂)` realizing `ρ` (the candidate functional is built FROM such a pair in
  the placement, so the pair is in hand, not re-chosen).
- `ιo`-summands (the old block `ro`) → their `Gv`-edge indices.

`j`'s **injectivity IS a leaf (L5)** — the candidate analog of `hjinj` (CaseI.lean:2768): `ιn`/`Unit`
use `e_a`/`e_b` (the two NEW edges through `v`, distinct since `eₐ ≠ e_b`), `ιo` uses `Gv`-edges (none
equal to `eₐ`/`e_b`, since those link `v ∉ V(Gv)` — the `hso_ne_eb` argument, extended to also exclude
`e_a`). Three pairwise-disjoint edge-supports ⟹ injective. `…_index` then closes: reindex independence
across `Equiv.ofInjective j`, transfer count by `Nat.card_range_of_injective` — exactly what
`case_II_placement_eq612` does inline and what `hasFullRankRealization_of_independent_panelRow_index`
packages. The full target count is `D(|V|−1) = ((D−1)+1) + D(|V_v|−1)` (the `+1` over the eq.-(6.12)
brick's `D(|V|−1)−1` is the `Unit` summand).

#### §1 question 3 — transport through `G − v` (N7b-2): reusable VERBATIM

`case_II_placement_eq612`'s old-block transport (`exists_independent_panelRow_transport Gv G ends ends
q₀ q₀ (f := id) injective_id (fun i => rfl)`, CaseI.lean:2700) is reused **verbatim** by the candidate
path: the old block `ro` is identical (the candidate placements `p₂`/`p₃` change only `v`'s normal /
the column-op, never the `Gv`-block, which the IH rigidity quantifies over `V(Gv) = V(G)∖{v}`,
motions avoiding `v`). What is NEW is only the `+1` candidate summand's membership (L4) — and that is
NOT a transport (it is a direct `G`-link `hG_ea`), so N7b-2 needs no extension. The common-subgraph
`G − v` machinery (`removeVertex_le` / `removeVertex_le_splitOff`) is not even invoked directly here —
it is the *justification* that `f := id` is valid (both frameworks sit above `G − v`), already baked
into the green N7b-2.

**Verdict:** L0 (the green-modulo skeleton) is the smallest first commit; it converts the blob into
L1–L5, isolates the §38 trap to L3, and reuses N7b-2 verbatim. No new generic helper is needed UNLESS
L3 walls (then `panelRow_ofNormals_candidate_eq`, §38). Compress to a pointer in `notes/Phase22g.md`.

> **§1.34's L-wire framing is SUPERSEDED by §1.35 below.** The L0/L1/L2/L4/L5-inj *bricks* are
> green and correct — they build the eq.-(6.12) `D(|V|−1)−1` panelRow blocks `so`/`sn` and their
> packaging. What §1.34 got wrong is the *device feed* it routes the finished candidate family
> through: it assumes the L0 spine's `hfamᵢ = panelRow ∘ jᵢ` contract (every row a single
> `panelRow`) can be met by the candidate completion. It cannot — KT's `+1` candidate row is
> provably **not** a single `panelRow` (it is the row-operation output `r̂`, with `r̂(C(e_b)) ≠ 0`,
> while every `panelRow` annihilates its edge's extensor). §1.34's L3/L5-pack `annihRow(C(e_a))`
> route and the whole "feed `hasFullRankRealization_of_independent_panelRow_index`" plan are off
> the live route. §1.35 corrects the feed; the corrected verdict is the live one.

---

### 1.35 The `d=3` L-wire — corrected candidate-row placement + device feed (2026-06-07)

Reading KT §6.4.1 eqs. (6.24)–(6.44) against the green Lean pins the L-wire down. Three settled
findings; each verified against both KT and the Lean.

**(1) The candidate-row placement geometry — final answer (resolves the "re-examine" fork).**
KT eq. (6.29)'s top-left full-rank `D×D` block for `R(G,p₁)` consists of the `va`-rows
`r(p₁(va))` (the new block at `e_a`, genuine `panelRow`s) **plus** the single row at `(vb)i*`
equal to `r̂ := ∑_j λ_{(ab)j} r_j(q(ab))` (eqs. (6.27)/(6.28), the redundant-row collapse). The
producer models this exactly: `linearIndependent_sum_p2_candidateRow` (and the `Φ`-operated
`linearIndependent_sum_augment_candidateRow`) place the candidate row **`hingeRow v b r̂`**
(resp. `hingeRow v a r̂` after the column op), where `r̂ : Module.Dual (ScrewSpace 2)` is the
Claim-6.12 common vector with the selector `r̂(C(e_b)) ≠ 0` (`linearIndependent_sumElim_candidateRow_iff`).
- **The placed row is NOT a `panelRow`** (closing (g1)): a `panelRow ends (e_b, t₁, t₂)` has
  functional `annihRow C(e_b) t₁ t₂`, which annihilates `C(e_b)` (`annihRow_apply_self`); `r̂`
  does not (`r̂(C(e_b)) ≠ 0`). So §1.34's L3 (`panelRow_eq_hingeRow_annihRow_of_ends`, which needs
  `ρ = annihRow C`) does not fire on the placed row. **It IS in `span rigidityRows`**, though:
  `hingeRow v b r̂ = ∑_j λ_{(ab)j} hingeRow v b r_j` (hingeRow linear in the functional), and each
  `r_j ∈ (span C(e_b))^⊥` makes `hingeRow v b r_j` a `panelRow` at `e_b`, a rigidity row. So the
  placed row is a *combination* of `e_b`-panelRows (closing (g2)) — a rigidity-row-span member, not
  a single panelRow.
- **`exists_candidate_row_eq612` is about a DIFFERENT `ρ`.** Its `ρ` is a *block* functional
  (`ρ ∈ (span C(e_b))^⊥`, the inductive `(ab)`-part `wGv = hingeRow a b ρ`), and its collapse
  `hingeRow v b ρ − wGv = hingeRow v a ρ` is the matrix-level row operation (eq. (6.27)) that
  produces the eq.-(6.29) *shape*. It is **not** the producer's `r̂`-row — the phase note's earlier
  "swap `hingeRow v b r̂` by the collapse `hingeRow v a ρ`" conflated the two functionals. The swap
  core `linearIndependent_sumElim_candidateRow_swap` (`w' − w ∈ span base`) **cannot** swap the
  `r̂`-row for a single panelRow either: a panelRow at `e_b` lies in `span(base)` while `r̂`-row does
  not (the family is independent), so they are in different cosets. The placed `r̂`-row is genuinely
  fresh — no single-panelRow substitute exists. (The swap core stands as a reusable lemma but is
  **off the live device-feed route**; it would matter only to a panelRow-shaped feed, which §1.35
  abandons.)

**(2) The device-feed fork — DECIDED: a corrected route (A), built on `exists_good_realization_const`
(NOT `_ofParam`).** The prompt's central factual question — is the literal `panelRow` shape
load-bearing in the device closure beyond `hcoord`/`hindep`? — is **YES** for the `_ofParam`/
`hasFullRankRealization_of_independent_panelRow[_index]` closure: its genericity argument coordinatizes
the row family as the degree-2 panel polynomials `c i j = annihRowPoly …` in the free normals (`hg`,
GenericityDevice.lean:215–230), an identity that holds *only* for `g q i = panelRow ends i`. A bare
`span ⊆ rigidityRows` family has no such polynomial coordinatization, so the phase note's route (A)
(relax `_index` to span-⊆-rigidityRows) does **not** work as a drop-in — and route (B) (realize the
`r̂`-row as a single panelRow) is impossible by (1). **But the device is not intrinsically about
panelRows.** `HasFullRankRealization k G := ∃ Q, Q.graph = G ∧ Q.toBodyHinge.IsInfinitesimallyRigidOn
V(G)` asks for *some* rigid framework, not a generic one — so the candidate completion produces the
**fixed** degenerate placement `ofNormals G ends q₀ᵢ` and proves it rigid at that fixed `q₀ᵢ`, via:
- **`exists_good_realization_const`** (CaseI.lean:2100, GREEN) — runs the device on the *constant*
  family (`σ := Unit`, `F p ≡ F₀`, polynomial coords the constants `C(φ(a i) j)`, so `hg` is
  `eval_C` and **no `annihRowPoly`/panelRow shape is needed**). It consumes a fixed `F₀`, an
  arbitrary finite family `a` with `span (range a) = span F₀.rigidityRows` (`hspanrows`) and an
  independent subfamily `s`, and gives `#s + dim Z(F₀) ≤ D|α|`. Weaken `hspanrows` to `≤` (the
  `hcoord` leg uses only `dualCoannihilator_anti`, so `span (range a) ≤ span rigidityRows` suffices —
  a one-line sibling, or relax `_const` in place).
- then `isInfinitesimallyRigidOn_vertexSet_of_finrank_le` (Pinning.lean:1344, GREEN, the same N3
  adapter `_ofParam` uses) turns `#s = D(|V|−1)` into `IsInfinitesimallyRigidOn V(G)`.

So the corrected device-feed variant is `hasFullRankRealization_of_independent_rigidityRow`-style but
built **on `_const`, at a fixed framework**, consuming the candidate completion's `Sum`-indexed
family `(rn ⊕ {hingeRow v b r̂}) ⊕ ro` directly (independence from the producer; span-⊆-rigidityRows
because every member is a rigidity row or a combination of `e_b`-panelRows by (1); count `D(|V|−1)`).
*No genericity, no row-swap, no panelRow re-shaping.* This also means the L0 spine
`case_III_hsplit_producer`'s `hfamᵢ = panelRow ∘ jᵢ` hypotheses are the **wrong contract** and must
be restated to carry the candidate families as `span-⊆-rigidityRows` + independent + counted (L0 is
green-modulo, so this is a signature edit on a not-yet-consumed skeleton, not a re-proof).

**(3) Abstract `F` requirement (§38).** Confirmed: the `r̂`-independence producers
(`linearIndependent_sum_p2/p3/augment_candidateRow`) are **graph-free over an abstract
`F : BodyHingeFramework`** (they read only `hingeRow`/`columnOp`/`hingeRowBlock`/`supportExtensor`),
so the §38 `ofNormals`/`withGraph` defeq-timeout trap does not bite them. `exists_good_realization_const`
is likewise abstract in `F₀`. The single point where `F` is instantiated to the concrete
`ofNormals G ends q₀ᵢ` carrier is the **final** device-feed call (the corrected variant), and the
`span-⊆-rigidityRows`/membership facts feeding it (L1/L2/L4 already discharge these at `ofNormals`,
green) — so the single-candidate brick states everything over abstract `F` and instantiates only at
that last step, per TACTICS-QUIRKS §38.

**Corrected leaf sequence (bottom-up, each a smallest-buildable commit):**
- **C1 — the fixed-framework device-feed variant.** `hasFullRankRealization_of_independent_rigidityRow`
  (GenericityDevice.lean): fixed `F₀ = ofNormals G ends q₀`, an independent family `f : ι →
  Module.Dual` with `span (range f) ≤ span F₀.rigidityRows` and `D(|V(G)|−1) ≤ |ι|`, gives
  `HasFullRankRealization k G`. Built on `exists_good_realization_const` (weaken its `hspanrows`
  to `≤`) + `isInfinitesimallyRigidOn_vertexSet_of_finrank_le`. Abstract; the analog of
  `hasFullRankRealization_of_independent_panelRow` for a non-panelRow family at a *fixed* placement.
- **C2 — the single-candidate brick (abstract `F`).** Compose, over abstract `F`: the `r̂`-family
  producer (`linearIndependent_sum_{p2,p3,augment}_candidateRow`, the `hr : r̂(C(e)) ≠ 0` direction),
  the `span-⊆-rigidityRows` fact for the assembled family (`rn`/`ro` panelRows are rigidity rows;
  `hingeRow v b r̂ = ∑ λ_j hingeRow v b r_j ∈ span rigidityRows` via the block-row combination of
  (1), using `span_annihRow_eq_dualAnnihilator` for the `r_j ∈ (span C(e_b))^⊥` membership), the
  count `D(|V|−1)`, then C1. Output: each candidate `r̂(Cᵢ) ≠ 0 → HasFullRankRealization`.
- **C3 — re-wire L0 + supply Claim-6.12 data.** Restate `case_III_hsplit_producer`'s carried
  per-candidate hypotheses from `hfamᵢ = panelRow ∘ jᵢ` to the C2 conclusion
  (`r̂(Cᵢ) ≠ 0 → HasFullRankRealization k G`), so the body is `case_III_eq629_conditional`'s
  disjunction mapped through the three C2 bricks (no device call in the spine — C2 already concludes
  the realization). Supply `hr`/`hp`/`hduality`/`Cᵢ` from the redundant-row decomposition
  (`exists_redundant_panelRow_ab_decomposition` builds `r̂ = ∑ λ_{(ab)j} r_j`, nonzero by `λ_{(ab)i*} = 1`)
  + the N3b duality (`case_III_claim612`'s `hduality`, green via 22f); the selector `r̂(Cᵢ) ≠ 0 ⟺ block
  full rank` is `linearIndependent_sumElim_candidateRow_iff`. The L1 blocks `so`/`sn`, L2 span bridge,
  L4 membership feed C2's `span-⊆-rigidityRows`/`hold`/`hspan` inputs verbatim.
- **C4/C5 — `theorem_55` `d=3`-instance node (B.2) + the `lem:case-II-realization`/`lem:case-III`
  flips**, then the Thm 5.5→5.6 push, as before.

**Verdict:** C1 (the fixed-framework `_const`-based device-feed variant) is the smallest first
commit — it is the keystone the corrected route turns on, and it is a thin composition of two green
lemmas. §1.34's L0–L5 bricks survive as the row-block infra C2 consumes; only the device-feed and
the L0 `hfamᵢ` contract change. Compress to a pointer in `notes/Phase22g.md`.

---

### 1.36 The `hduality` six-join modeling subtlety — restate to the per-panel-line model (route (a)) (2026-06-08)

Building the per-line N3b brick (`extensor_join_eq_zero_of_complementIso_eq_zero_dotProduct`, C5b's
verified ingredient) surfaced a red-node-consistency question on `case_III_claim612`'s `hduality`
hypothesis. This is the resolution (canonical home; `notes/Phase22g.md` carries the ≤3-line verdict +
pointer). Verified against KT §6.4.1 eqs. (6.42)–(6.45) (printed pp. 690–691), the green
`case_III_claim612` proof, the per-line brick, and N3a (`exists_affineIndependent_panel_incidence`).

**The shape as currently stated (RigidityMatrix.lean:1519).** `case_III_claim612` carries
`hduality : r C₁ = 0 → r C₂ = 0 → r C₃ = 0 → ∀ q : {q // q.1 < q.2}, r (omitTwoExtensor (homogenize ∘
p) …) = 0`, with three **fixed** `C₁ C₂ C₃ : ScrewSpace 2` (= the three candidate hinge support
extensors `F.supportExtensor e`, each itself a panel-meet `complementIso (n_u ∧ n_v)`). The green
proof is honest — it forwards `hduality` to `eq_zero_of_annihilates_span_top
(span_omitTwoExtensor_eq_top hp)`. Both downstream consumers (`case_III_eq629_conditional`:1564,
`case_III_hsplit_producer`, CaseI.lean:3640) likewise *forward* `hduality` as an explicit hypothesis;
**nobody discharges it.** The discharge obligation lives at C5 (the producer's carried data).

**Why it is undischargeable as stated (decisive).** `ScrewSpace 2 = ⋀²ℝ⁴` has `finrank = 6`. Three
`2`-extensors `C₁,C₂,C₃` span a subspace of dimension `≤ 3`, so `r ⊥ C₁,C₂,C₃` is satisfiable by a
nonzero `r` (the orthogonal complement is `≥ 3`-dimensional). Hence "`r C₁=0 → r C₂=0 → r C₃=0 →
r ⊥ (all six joins, which span 6 dims)`" cannot be proved from the three fixed `Cᵢ` alone — it would
force `r = 0` on a satisfiable premise. This is *strictly stronger* than the previous agent's framing
("can't reach the three single-panel opposite joins"): with the brick fixing each join's line, the
fixed `Cᵢ` reach *no* join whose line ≠ a `Cᵢ`-line. **Route (c) — "three fixed `Cᵢ` are
sufficient" — is decisively wrong.**

**What KT actually does (the per-panel-line quantification).** Claim 6.12 (p. 690): "at least one of
`M₁,M₂,M₃` has full rank **for some choice** of lines `L ⊂ Π(a)`, `L' ⊂ Π(b)`, `L'' ⊂ Π(c)`." The
contrapositive negates the existential: for **all** choices, all three blocks fail, giving (eqs.
(6.42)–(6.44)) `r ⊥ C(L)` for *every* `L ⊂ Π(a)`, every `L' ⊂ Π(b)`, every `L'' ⊂ Π(c)` — i.e.
`r ⊥` the entire union (6.45) `(∪_{L⊂Π(a)} C(L)) ∪ (∪_{L'⊂Π(b)} C(L')) ∪ (∪_{L''⊂Π(c)} C(L''))`. KT
then takes four affinely-independent points `p0 = Π(a)∩Π(b)∩Π(c)`, `p1 ∈ Π(a)∩Π(b)∖Π(c)`,
`p2 ∈ Π(b)∩Π(c)∖Π(a)`, `p3 ∈ Π(a)∩Π(c)∖Π(b)`; *every* join-line `pᵢpⱼ` lies in `Π(a)∪Π(b)∪Π(c)` (each
endpoint pair shares ≥ 1 panel), so each join's `C(pᵢpⱼ)` is a member of (6.45). Lemma 2.1 ⟹ the six
joins span `⋀²ℝ⁴`, so `r = 0`. **The quantification is genuinely per-panel-line; the three fixed
candidate-hinge `Cᵢ` are not the annihilated family — the union (6.45) is.**

**N3a panel-incidence data (`exists_affineIndependent_panel_incidence`, green).** Supplies three panel
normals `n : Fin 3 → Fin 4 → ℝ` (`LinearIndependent`, the "nonparallel" hypothesis) for Π(a)/Π(b)/Π(c)
and four affinely-indep points `p : Fin 4 → Fin 3 → ℝ` with incidence `p i ∈ Π(u) ⟺
homogenize (p i) ⬝ᵥ n u = 0`. Tabulated orthogonality: `p0 ⊥ {n0,n1,n2}`, `p1 ⊥ {n0,n1}`,
`p2 ⊥ {n1,n2}`, `p3 ⊥ {n0,n2}`. The six joins and their common normals: `p0∨p1: {n0,n1}`,
`p0∨p2: {n1,n2}`, `p0∨p3: {n0,n2}` (two common normals each) and `p1∨p2: {n1}`, `p1∨p3: {n0}`,
`p2∨p3: {n2}` (one common normal each). The per-line brick `…_dotProduct` takes two normals `{n_u,n'}`
and transfers `r(complementIso (n_u∧n')) = 0 ⟹ r(pᵢ∨pⱼ) = 0` when both points are ⊥ both normals.

**The fix — route (a): restate `hduality` to the per-panel-line model.** Replace the three-fixed-`Cᵢ`
premise with KT eq. (6.45)'s honest quantification, keyed off the N3a data. The natural restated
premise (to be pinned at build time against the brick's exact signature, C5a): for each of the six
joins, the line lies in some panel `Π(u)`; the dispatch (C5b) supplies, per join, a *second* normal
`n'` (a second hyperplane through the join-line within `Π(u)`) so the brick fires. The three through-p0
joins use two N3a panel normals directly; the three opposite joins (single panel) take their second
normal from the panel's line-sweep that the restated premise carries (KT's "any `L ⊂ Π(u)`"). The
**conclusion is unchanged** (`r C₁≠0 ∨ r C₂≠0 ∨ r C₃≠0`, the disjunction the producer's
candidate-selection needs). Route (b) ("enrich the producer's hypothesis") is the *same* edit: both
consumers forward `hduality`, so the restate ripples identically through `case_III_eq629_conditional`
and `case_III_hsplit_producer` with **no proof-body change** (each is a `.imp`/`rcases` over the
disjunction the conclusion still provides).

**Exact-premise caveat (flagged for the build).** The precise Lean shape of the restated `hduality`
(how the "any second hyperplane through the line" is quantified — per-join `∃ n'` carried as data, vs.
a uniform per-panel `∀ L ⊂ Π(u)` indexed family) is a small design call best made *at the C5a build*
against the per-line brick + the disjunction-input the contrapositive needs; both candidate shapes are
discharge-feasible (the brick fires either way), and the C5b assembly is graph-free. This is a shape
refinement *within* the decided route (a), not a re-open of the (a)/(b)/(c) verdict.

**Blueprint consistency.** The N3b node `lem:case-III-claim612-line-in-panel-union` (case-iii.tex:871)
**already** states the per-panel-line model honestly ("a screw functional `r` that annihilates *every*
panel-meet extensor `C(L)` of lines `L ⊂ Π(a)∪Π(b)∪Π(c)` also annihilates each spanning join"), and
the `lem:case-III-claim612` node (case-iii.tex:1088) does not commit to a fixed-`Cᵢ` shape. **No
blueprint prose is wrong** — the divergence was Lean-only (the `hduality` hypothesis narrowed past
what the dep-graph describes). No `.tex` edit needed.

---

### 1.37 The `hann` discharge — verdict (B): `hduality`'s *antecedent* is mis-shaped; restate to the line-swept block-failure premise (2026-06-09)

> **Scope estimate superseded by §1.38 (2026-06-09, same day, coordinator re-adjudication).** §1.37's
> *diagnosis* (the three-fixed antecedent is undischargeable; not circular but under-powered) and its
> B1 restate of `case_III_claim612` itself **stand and are re-confirmed**. What §1.38 revises: §1.37's
> "~2 commits, only a quantifier" estimate for the producer's `hann` derivation (C5c-step-2) — that
> step is a **re-parameterization of the candidate construction over a free line `L ⊂ Π(u)`** (the
> three-fixed-seed `q₁/q₂/q₃` carriage must become line-indexed to *supply* `hann`), a multi-commit
> producer-internal restructure, not a one-line quantifier addition. Read §1.38 for the live scope.

The C5a/C5b restate (§1.36, `d851264`) made `hduality`'s **conclusion** honest (the per-join witness
form) but **left its antecedent the three fixed scalars `r C₁ = 0 → r C₂ = 0 → r C₃ = 0`.** Tracing
the `hann` discharge — never analyzed by the §1.33 / §1.35 / §1.36 recons — shows this antecedent is
the *same* mis-shaping the conclusion had, in the half that was not fixed. Verdict: **(B), but a
LOCAL restate, not a phase-boundary re-architecture.** Verified against KT pp. 690–691 (eqs.
(6.42)–(6.45)), `case_III_claim612` (RigidityMatrix.lean:1626), the C5c assembly
`exists_hduality_witness_of_panel_incidence` (:1679), `case_III_hsplit_producer` (CaseI.lean:3641),
and `mem_hingeRowBlock_iff` (:1262).

**The gap, decisively (not circular, but under-powered).** `exists_hduality_witness_of_panel_incidence`
produces `case_III_claim612`'s per-join witness *modulo* `hann`:
`∀ u (m), LinearIndependent ![n u, m] → r (complementIso ⟨extensor ![n u, m], _⟩) = 0` — i.e.
`r ⊥ C(L)` for **every** line `L ⊂ Π(u)`, all three panels (KT's union (6.45), exactly). But the
*only* thing the contrapositive of `case_III_claim612`'s carried `hduality` supplies is its
antecedent `r C₁ = r C₂ = r C₃ = 0` — `r ⊥` the **three fixed candidate-hinge supports**
`Cᵢ = F.supportExtensor eᵢ` (`mem_hingeRowBlock_iff`: block-fail at edge `e` gives exactly the one
scalar `r(supportExtensor e) = 0`). Three `2`-extensors span ≤ 3 of the 6 dims, so `r ⊥ C₁,C₂,C₃`
**cannot** give `hann` (§1.36's own dimension count). So `hduality`-as-stated is *undischargeable from
its own antecedent*: the `r Cᵢ = 0` premises are dead weight. **Not circular** — discharging it does
not reduce to re-proving the conclusion — it is simply *under-powered*: the antecedent that `hann`
needs ("all three blocks fail for **every** line choice `L`") is strictly stronger than the
three-fixed-scalar premise the §1.36 restate left in place.

**What KT actually quantifies (the per-line freedom).** KT p. 690: `p₁(va) = L`, `p₂(vb) = L'`,
`p₃(ac) = L''`, *"where we **may choose any** (d−2)-dimensional affine subspaces `L ⊂ Π(a)`,
`L' ⊂ Π(b)`, `L'' ⊂ Π(c)`"*. The candidate block `Mᵢ` is **parameterized by the line choice**; the
candidate vector `r̂ := ∑_j λ_{(ab)j} r_j(q(ab))` is **fixed across all choices** (it reads only the
inductive `ab`-data). "Mᵢ fails for choice `L`" ⟺ `r̂ ⊥ C(L)` (row-space criterion, KT (6.42)).
Claim 6.12 is the **existential over line choices**: *at least one of M₁/M₂/M₃ has full rank **for
some choice** of `L,L',L''`.* Its contrapositive is "all blocks fail for **all** choices" → `r̂ ⊥`
the whole union (6.45) → (Lemma 2.1, four affinely-indep points) `r̂ = 0`. **The Lean's three fixed
`C₁,C₂,C₃` are three SPECIFIC line choices, not the existential** — so the conclusion
`r C₁≠0 ∨ r C₂≠0 ∨ r C₃≠0` is *narrower* than KT's "∃ line choice, block full rank", and the
antecedent `r C₁=C₂=C₃=0` is *weaker* than KT's "fail for all `L`". Both halves are the same fixed-vs-
swept mis-shaping; §1.36 caught it on the conclusion's *join* side and fixed that, but the
**candidate/`Cᵢ`** side stayed fixed.

**The fix (LOCAL — a signature restate of `case_III_claim612`, mirroring §1.36's edit on the other
half).** Replace the dead three-scalar antecedent with the line-swept premise that the producer can
actually deliver and the assembly actually needs. Two discharge-feasible shapes (pin the exact one at
build against the assembly's signature; both are graph-free):
- **(B1, recommended) carry `hann` directly as the premise.** `case_III_claim612`'s `hduality`
  antecedent becomes the union form `∀ u m, LinearIndependent ![n u, m] → r(complementIso ⟨extensor
  ![n u, m],_⟩)=0` (= the assembly's `hann`), keyed off N3a normals `n`. Then `hduality`'s body is
  *literally* `exists_hduality_witness_of_panel_incidence` (already built), and the conclusion stays
  the **existential** `∃ u (line choice), r̂(C(L)) ≠ 0` — or, kept concrete, the producer's needed
  form (see ripple). The body of `case_III_claim612` becomes: contrapositive → `hann` → assembly →
  `span_omitTwoExtensor_eq_top` → `r=0` ⨯ `hr`. This is the faithful KT encoding.
- **(B2) carry the per-line block-failure family.** Premise = `∀ u (L ⊂ Π(u)), block(L) not full rank`,
  phrased as `∀ u m indep, r̂(complementIso (n u ∧ m)) = 0` — definitionally the same as `hann` after
  `mem_hingeRowBlock_iff`, so B2 collapses to B1. No separate value.

So the *real* edit is: **`hduality`'s antecedent `r C₁=0→r C₂=0→r C₃=0` → `hann` (the union premise),
and `case_III_claim612`'s body = the C5c assembly** (which is why the assembly was built taking `hann`:
it IS the body). The three fixed `Cᵢ` then appear *only* in the conclusion the producer's
candidate-selection consumes.

**The conclusion + producer ripple — the one genuine design call.** KT's faithful conclusion is the
existential `∃ line choice, block full rank`. But the producer (`case_III_hsplit_producer`) builds
**three concrete candidate placements** (edges `va`/`vb`/`ac`, supports `C₁`/`C₂`/`C₃`) and consumes
the *three-fixed* disjunction `r̂ C₁≠0 ∨ r̂ C₂≠0 ∨ r̂ C₃≠0`. Resolve as follows:
- The producer's three fixed candidates are KT's existential **instantiated at three specific lines**
  — the degenerate eq.-(6.12) placements at `va`/`vb`/`ac`. The contrapositive that *feeds* `hann`,
  however, must range over **all** lines, which the three concrete placements do **not** witness by
  themselves. **The producer cannot supply `hann` from its three blocks.** Therefore `hann` must come
  from the **redundant-row / eqs.-(6.42)–(6.43) machinery directly**: for an *arbitrary* line `L ⊂ Π(u)`,
  the candidate block built from `L` has its `D−1` rows spanning `(span C(L))^⊥` (`hspan` of the
  selectors, but now at the swept line), and the *fixed* `r̂` lies in that block exactly when
  `r̂(C(L)) = 0`. So `hann` is **not** "all three fixed blocks fail" — it is the statement that for
  every line `L` in each panel, the (D−1) panel rows at `L` already span `(span C(L))^⊥` and `r̂` is
  among them iff `r̂(C(L)) = 0`, which is the **per-line block-failure premise of Claim 6.12 KT
  quantifies over**. This is genuinely *new* obligation content (the swept block-failure), but it is
  the SAME row-space criterion (`mem_hingeRowBlock_iff` / `linearIndependent_sumElim_candidateRow_iff`)
  applied at an arbitrary `L` rather than the three fixed edges — no new machinery, only a quantifier.
- **Cleanest shape:** `case_III_claim612` keeps the three-fixed conclusion `r C₁≠0 ∨ r C₂≠0 ∨ r C₃≠0`
  (what the producer's selectors consume, unchanged), and takes `hann` as its premise (B1). The
  producer's obligation to *supply* `hann` then becomes a NEW carried hypothesis on
  `case_III_hsplit_producer` (the union annihilation, at the real `ofNormals` `r̂`/normals data),
  discharged by a NEW leaf that runs the row-space criterion over an arbitrary line. This is the
  honest decomposition: `case_III_claim612` becomes *trivially green* (body = the assembly + span-top
  + `hr`); the genuine remaining math (the swept block-failure → `hann`) moves to the producer's
  carried data, exactly where C5c already lives.

**Ripple (all local, no phase boundary).**
- `case_III_claim612` (RigidityMatrix.lean:1626): antecedent `r C₁=0→r C₂=0→r C₃=0` ⟹ `hann`-shaped
  union premise (keyed off N3a `n`, `h0`/`h1`/`h2`/`h3` incidence); body ⟹ the C5c assembly +
  `span_omitTwoExtensor_eq_top` + `hr`. Conclusion unchanged. `C₁ C₂ C₃` move to the conclusion only.
- `case_III_eq629_conditional` (RigidityMatrix.lean:1791) + `case_III_hsplit_producer` (CaseI.lean:3641):
  forward the new `hann`-shaped `hduality` premise verbatim (same pure-signature ripple §1.36 had —
  both `.imp`/`rcases` the unchanged conclusion). `case_III_hsplit_producer` gains the `hann` premise
  (+ N3a `n`/incidence) as carried data; its body is unchanged (`rcases case_III_claim612 …`).
- The three selector recasts (`linearIndependent_sum_{p2,p3,augment}_candidateRow_selector`) and C1/C2/
  C3 are **untouched** — they consume the *conclusion* (`r̂ Cᵢ ≠ 0`), which does not change.
- The C5c assembly `exists_hduality_witness_of_panel_incidence` is **already exactly the new body** —
  built taking `hann`, it was constructed for precisely this shape. No rebuild.
- The genuine remaining math (now correctly located): a NEW leaf deriving `hann` at real `ofNormals`
  data = the swept eqs.-(6.42)–(6.43) block-failure → `r̂ ⊥ C(L)` for every `L`. This is the "C5c-(i)"
  work, unchanged in difficulty but now correctly stated as the producer's carried obligation rather
  than miscast as `hduality`'s dead three-scalar antecedent.

**Estimate: ~2 commits.** (1) the `case_III_claim612` antecedent→`hann` restate + body=assembly +
the two-consumer signature ripple (one green unit, mirrors §1.36's C5a/C5b); (2) the swept-line `hann`
derivation leaf at real data (the genuine C5c-(i) math — may itself split, see hand-off). The fixed
`hann`-as-premise step (1) is buildable now (the assembly exists); step (2) is the deferred core.

**Blueprint consistency.** `lem:case-III-claim612`'s statement + proof prose (case-iii.tex:1086–1134)
**already** describes exactly the line-swept model: "Suppose all three blocks fail to have full rank
for *every* choice of lines … `r ∈ (span C(L))^⊥` for all `L ⊂ Π(a)`", and the explicit aside
(1130–1133) that `hduality` is "the union form … **not** the three fixed candidate-hinge supports
`C₁,C₂,C₃`". So the **blueprint is correct and the Lean is what diverges** — the `hduality`
*antecedent* still carries the three fixed scalars the prose explicitly disavows. The honesty gate
verdict: `lem:case-III-claim612`'s `\leanok` is currently **dishonestly green** on its antecedent
(the carried `hduality` does not match the prose's union form), the mirror of the conclusion-side
issue §1.36 fixed. Flagging as a blueprint↔Lean divergence to reconcile when (B1) lands; no `.tex`
edit needed (the prose is already the target shape — the Lean must catch up to it). Tracked in
`notes/Phase22g.md` Blockers.

---

### 1.38 The `hann`-discharge re-adjudication — CONFIRM the gap, REFUTE the three-fixed-suffices escape; §1.37's B1 holds for `case_III_claim612` but the producer's `hann` derivation is a genuine restructure, not "only a quantifier" (2026-06-09)

> **FIX SHAPE SUPERSEDED by §1.39 (2026-06-09, same-day coordinator design pass).** §1.38's
> *diagnosis* (the three-fixed antecedent is undischargeable; dimension 3 < 6; the producer's real
> work is a line-indexed candidate re-parameterization) **stands and is re-confirmed by §1.39.** What
> §1.39 overturns is §1.38's *fix shape* — "keep the three-fixed disjunction conclusion + carry `hann`
> as a premise discharged by the C5c assembly" (B1). The cleaner, KT-faithful fix is to restate
> `case_III_claim612` to the **existential conclusion with NO `hann`/`hduality` premise** (the
> coordinator's call, verified). That makes the C5c six-join assembly + its two bricks **obsolete on
> the `d=3` live route**. Read §1.39 for the live architecture + leaf sequence; the producer-internal
> restructure (C5c-(2)) is identical in difficulty under both shapes.

> **Dated supersession of §1.37's scope estimate.** This recon re-opens §1.37 at a coordinator's
> request (its B1 fix "likely does not close"). **Verdict: §1.37's *diagnosis* and its B1 restate of
> `case_III_claim612` itself are CORRECT and survive; its *scope estimate* ("~2 commits, only a
> quantifier") is REVISED** — the genuine remaining work (the producer's `hann` derivation, the
> deferred C5c-step-(2)) is a **re-parameterization of the candidate construction over a free line
> `L ⊂ Π(u)`**, materially bigger than "add a quantifier." Read this section as the live scope; §1.37's
> 2-commit estimate is superseded.

**The objection adjudicated (verified against KT pp. 678/690–691 + the green Lean).** A coordinator
objection holds that (i) `case_III_claim612` carries `hduality`/`hann` as a supplied premise the
producer must discharge, (ii) `hann` (= `r ⊥ C(L)` for *every* panel line) spans `⋀²ℝ⁴` so forces
`r = 0`, false for the real `r̂ ≠ 0`, hence undischargeable from a three-fixed antecedent, and (iii)
the fix changes the conclusion to KT's existential and restructures the producer. **The prompt's
linchpin escape** — that the producer's *three graph-fixed* candidates `C₁=C(va)/C₂=C(vb)/C₃=C(ac)`
might *suffice* via a forced relation with `r̂` (so the three-fixed disjunction is provable without
sweeping all lines) — **is REFUTED decisively:**

- **KT eq. (6.12) + Claim 6.9 + eq. (6.42) (printed pp. 678, 690):** `p₁(va) = L` where **"`L` is a
  `(d−2)`-affine subspace contained in `Π(a)`"** and "(G,p₁) is a panel-hinge realization **for any
  choice** of `L ⊂ Π(a)`"; eq. (6.42) writes `M₁ = (r(L); r̂)`, `M₂ = (r(L'); r̂)`,
  `M₃ = (r(L''); −r̂)` with **"we may choose any `L ⊂ Π(a)`, `L' ⊂ Π(b)`, `L'' ⊂ Π(c)`."** The three
  candidate placements are at **freely-chosen lines**, *not* three graph-fixed extensors. Claim 6.12 is
  the **genuine existential over the continuum of line choices** ("for some choices of `L, L', L''`");
  its contrapositive ("all blocks fail for **all** choices") is what gives the union (6.45), and
  Lemma 2.1 on four affinely-independent points forces `r̂ = 0`. There is **no forced relation** among
  `r̂` and three fixed `Cᵢ`.
- **Dimension count (numerically confirmed):** the full panel sweep `n₀∧ℝ⁴ + n₁∧ℝ⁴ + n₂∧ℝ⁴` spans **6
  dims** = `⋀²ℝ⁴`; **three fixed lines (one per panel) span ≤ 3 dims** (three vectors in a 6-dim space).
  So `r̂ ⊥ C₁,C₂,C₃` leaves a `≥ 3`-dim space of valid nonzero `r̂` — the three-fixed disjunction
  `r̂C₁≠0 ∨ r̂C₂≠0 ∨ r̂C₃≠0` is **not** a theorem for fixed `Cᵢ`. Escape refuted; objection (ii)
  CONFIRMED.

**Where §1.37's B1 is right (and the objection's "change the conclusion" demand is *not* needed).**
The objection (iii) overstates the fix for `case_III_claim612` *itself*. The current green proof
(RigidityMatrix.lean:1641–1656) does `by_contra → obtain ⟨h₁,h₂,h₃⟩ : r̂C₁=r̂C₂=r̂C₃=0 →
hr (eq_zero_of_annihilates_span_top … (hduality h₁ h₂ h₃))`; **`h₁/h₂/h₃` are consumed *only* to feed
`hduality`'s antecedent** — never to derive the contradiction. So if `hduality`'s antecedent is dropped
and `hann` becomes an **unconditional** premise (§1.37's B1), the proof still closes: by_contra still
produces `h₁/h₂/h₃` (now unused), and `hann → assembly → span-top → r̂=0 ⊥ hr`. **The three-fixed
conclusion `r̂C₁≠0 ∨ r̂C₂≠0 ∨ r̂C₃≠0` stays — and is provable from `hann`** (the disjunction is the
*conclusion* the producer's selectors consume; it need not become an existential, because the
contradiction lives in `hann ⟹ r̂=0`, not in the three scalars). So `case_III_claim612` is a ~1-commit
local restate, body = `exists_hduality_witness_of_panel_incidence` (already built taking `hann`). The
C5c assembly + the three selectors + C1/C2/C3 survive verbatim. **The objection's "`hann` internal
under a by_contra over an existential conclusion" is one valid encoding, but the carry-`hann`-as-premise
encoding (B1) is equally faithful and minimally disruptive — the conclusion need not change.**

**Where the objection is right and §1.37 understated — the producer's `hann` derivation (C5c-step-2).**
§1.37 already conceded "the producer cannot supply `hann` from its three blocks" and located the genuine
math in a NEW producer leaf, but called it "no new machinery, only a quantifier." **That understates
it.** `hann` is `∀ u (m indep from n u), r̂(complementIso (n u ∧ m)) = 0` — i.e. `r̂ ⊥ C(L)` for
*every* line `L ⊂ Π(u)`, all three panels. To derive this at the real `ofNormals` data, the producer
must run the row-space criterion (`mem_hingeRowBlock_iff` / `linearIndependent_sumElim_candidateRow_iff`)
**at an arbitrary line `L`**, where the candidate block's supporting extensor is `C(L)` — *not*
`supportExtensor e` at a fixed graph edge. But the current producer
(`case_III_hsplit_producer`, CaseI.lean:3641) carries **three fixed seeds `q₁/q₂/q₃`** and three fixed
`hmemᵢ`/`hcardᵢ`/`hselᵢ` keyed to the three candidate edges; `hingeRowBlock e = (span C(p(e)))^⊥` is
indexed by an **edge**, and `C(p(e))` is fixed by the seed. Deriving `hann` therefore requires the
candidate-block construction (the eq.-(6.12) placement + the `D−1` panel rows spanning `(span C(L))^⊥`)
to be **re-parameterized over a *family* of seeds indexed by the free line `L ⊂ Π(u)`** — the producer
must build the degenerate placement at an *arbitrary* `L`, not just the three graph-fixed edges. **That
is a structural reshape of the producer's carried data (a line-indexed candidate family), not a
one-line quantifier addition.** This is the genuine deferred core; it is where the real KT content of
Claim 6.12's existential lives.

**Verdict + scope.** Architecture call: **CONFIRM** the carried-`hduality`-as-three-fixed-premise is
undischargeable and **REFUTE** the three-fixed-suffices escape (KT's lines are free, not graph-fixed;
dimension 3 < 6). The fix splits cleanly:
- **(local, ~1 commit, buildable now) C5c-step-(1):** restate `case_III_claim612`'s `hduality`
  *antecedent* `r C₁=0→r C₂=0→r C₃=0` → the unconditional `hann` union premise (keyed off N3a normals
  `n`); body becomes `exists_hduality_witness_of_panel_incidence` + `span_omitTwoExtensor_eq_top` + `hr`.
  Conclusion unchanged (three-fixed disjunction). `case_III_eq629_conditional` + `case_III_hsplit_producer`
  forward verbatim (the producer gains `hann` + N3a `n`/incidence as carried data). Selectors + C1/C2/C3
  untouched. Reconcile the `lem:case-III-claim612` Lean↔prose divergence here (prose already correct).
  This is §1.37's B1 verbatim — it **does close** for the claim, contra the coordinator's worry.
- **(genuine restructure, the real remaining math) C5c-step-(2):** derive `hann` at real `ofNormals`
  data. **Not "only a quantifier"** — the producer's candidate construction (currently three fixed
  seeds) must be re-parameterized to build the eq.-(6.12) degenerate placement + its `(D−1)` panel rows
  at an **arbitrary line `L ⊂ Π(u)`**, then run the row-space criterion at `C(L)` to get `r̂ ⊥ C(L)` for
  every `L`. This re-parameterization is the structural work; it will likely split (the line-indexed
  placement family + the per-line block-failure + the panel-sweep assembly). **Scope flag: this is a
  multi-commit restructure of the producer's carried `hmemᵢ`/seed data, not the ~1-commit local edit
  §1.37 implied — but it does NOT change `case_III_claim612`, the selectors, C1/C2/C3, or the C5c
  assembly, and does NOT cross a phase boundary** (it is producer-internal, all within
  `case_III_hsplit_producer`'s discharge). Estimate: step-(1) = 1 commit; step-(2) = 3–5 commits
  (the line-indexed candidate-family reshape + per-line criterion + sweep). The C5c-(ii) OLD/NEW-block
  `hmemᵢ` work is independent and rides alongside.

**What survives / what reworks.** All landed C5 leaves survive: the C5c assembly
(`exists_hduality_witness_of_panel_incidence`), the two bricks (`exists_independent_perp_pair`,
`omitTwoExtensor_homogenize_eq_extensor_kept`), the three selector recasts, C1/C2/C3, `candidateRow_ne_zero`,
`candidateRow_ac_eq_neg`, the `r̂`-vector data — none reworks. The rework is **the producer's seed/`hmemᵢ`
carriage**: the three-fixed-seed `q₁/q₂/q₃` + `hmem₁/₂/₃`/`hcard₁/₂/₃` shape must become a line-indexed
family to *supply* `hann`. (The conclusion-consuming half — `hselᵢ`/C1/C2/C3 — is unchanged.)

---

### 1.39 The definitive `d=3` Case-III crux architecture — DROP `hann` entirely; restate `case_III_claim612` to the existential conclusion (coordinator's call CONFIRMED, supersedes §1.37/§1.38's B1) (2026-06-09)

> **Supersedes §1.37's B1 and §1.38's "keep three-fixed conclusion + carry `hann` as a premise".**
> §1.37/§1.38's *diagnosis* (the three-fixed antecedent `r C₁=0→r C₂=0→r C₃=0` is undischargeable;
> dimension 3 < 6; the producer's real work is a line-indexed candidate re-parameterization) **stands
> and is re-confirmed.** What this section overturns is the *fix shape*: §1.38's B1 kept the
> three-fixed disjunction `r̂C₁≠0 ∨ r̂C₂≠0 ∨ r̂C₃≠0` as the conclusion and carried `hann` as a premise
> discharged by the (already-built) C5c assembly. **That is not the cleanest fix.** The honest
> `case_III_claim612` is the **existential conclusion with no `hann`/`hduality` premise at all** — the
> coordinator's position, verified below against the actual Lean. This makes the C5c assembly + its two
> bricks **obsolete on the live route** (effort-accounting flag).

This is a build-free design-pass verdict. The deliverable is a buildable leaf sequence; the architecture
is pinned. Verified against the green Lean (`case_III_claim612` RigidityMatrix.lean:1626; the producer
CaseI.lean:3641; the selectors :1432/:1459/:1493; `hasFullRankRealization_of_candidateSelector`
CaseI.lean:2204; `toBodyHinge` PanelHinge.lean:87–97) and KT pp. 678/690–691, with `lean_multi_attempt`
on the existential proof skeleton (closes, `goals:[]`).

**(a) The cleanest `case_III_claim612` — existential conclusion, no premise.** Restate to:
```
theorem case_III_claim612 {r : Module.Dual ℝ (ScrewSpace 2)} (hr : r ≠ 0)
    {p : Fin 4 → Fin 3 → ℝ} (hp : AffineIndependent ℝ p) :
    ∃ q : {q : Fin 4 × Fin 4 // q.1 < q.2},
      r ⟨omitTwoExtensor (fun i => homogenize (p i)) (ne_of_lt q.2),
        extensor_mem_exteriorPower _⟩ ≠ 0
```
**No `C₁ C₂ C₃`, no `hduality`, no `hann`.** The ~5-line proof (verified to close via
`lean_multi_attempt`):
```
  by_contra h
  push Not at h
  exact hr (eq_zero_of_annihilates_span_top (span_omitTwoExtensor_eq_top hp)
    (by rintro x ⟨q, rfl⟩; exact h q))
```
i.e. *contrapositive of an existential*, reusing the **exact** machinery the current body already uses
(`span_omitTwoExtensor_eq_top` + `eq_zero_of_annihilates_span_top`). `hann` was never a supplied
premise — it is precisely the internal `by_contra` negation `h : ∀ q, r(join q) = 0`. This is what
§1.36's prose at case-iii.tex:1105 ("Suppose all three blocks fail … for *every* choice of lines") is
*about*: the union (6.45) annihilation is the negated existential, derived inside the proof, not
carried in. The existential ranges over the **six joins of the four affinely-independent points `p`**
only — it does **not** need the full line continuum (the joins already span via Lemma 2.1 /
`span_omitTwoExtensor_eq_top`, exactly the coordinator's recon). `hduality`/`hann` **vanish entirely**
(answers prompt (b): no residual premise survives on `case_III_claim612`).

**(b) Why this is consumable — the geometric identity that closes the gap.** A candidate hinge support
is `(ofNormals G ends q₀).toBodyHinge.supportExtensor e = panelSupportExtensor (normal u) (normal v)`
for `(u,v) = ends e` (PanelHinge.lean:89, `rfl`) — a **panel-meet**, the same `extensor`/`complementIso`
form as a join `pᵢ∨pⱼ` and as KT's `C(L)`. KT's three candidates split at the degree-2 bodies `v`
(along `va`,`vb`) and `a` (along `ac`); candidate `M₁`'s support is the meet of body `v`'s panel with
body `a`'s panel = a line `L ⊂ Π(a)` (KT eq. (6.12): `p₁(va) = L`, `L` freely chosen via the shear
`t`/seed `q₀`). So the producer's `Cᵢ` **are** freely-chosen lines, and a witness join `pᵢ∨pⱼ` is a
line in one of the three panels. **The producer consumes the existential by building its candidate
placement so its hinge line IS the witness join's line `pᵢpⱼ`** — choosing the four points `p` (which
`case_III_claim612` takes as a *parameter*, so the producer supplies them) adapted to the real three
panels. This is the same producer-internal re-parameterization §1.38 identified as the genuine deferred
core; the existential conclusion just states it faithfully instead of pre-fixing three concrete
disjuncts the producer can't deliver.

**(c) What survives, what is now OBSOLETE (effort-accounting, honest).**
- **Survive verbatim:** the contradiction core (`span_omitTwoExtensor_eq_top`,
  `eq_zero_of_annihilates_span_top`), `candidateRow_ne_zero` (`r̂ ≠ 0`), `candidateRow_ac_eq_neg`
  (eq. (6.44)), the `r̂`-vector data (`exists_redundant_panelRow_ab_lam`), C1
  (`hasFullRankRealization_of_independent_rigidityRow`), C2
  (`hasFullRankRealization_of_candidateSelector`), the row-space criterion
  (`linearIndependent_sumElim_candidateRow_iff` / `mem_hingeRowBlock_iff`), L1/L2/L4, the `+1`-row
  membership (`hingeRow_mem_rigidityRows`). None reworks.
- **OBSOLETE on the live route (built to discharge `hann`, which no longer exists):**
  `exists_hduality_witness_of_panel_incidence` (the C5c six-join assembly, `2bd5fa2`),
  `exists_independent_perp_pair` (`07c537c`), `omitTwoExtensor_homogenize_eq_extensor_kept` (`b031eb3`),
  `extensor_join_eq_zero_of_complementIso_eq_zero_dotProduct` (the N3b `⬝ᵥ`-form, `b8477db`), and the
  C5a/C5b `hduality` six-join dispatch baked into the current `case_III_claim612` body (`d851264`).
  These five leaves (the bulk of the last week's commits) were the machinery for *carrying and
  discharging* the per-join `hduality` witness; the existential restate dissolves that obligation into
  a one-line negated-existential. They stay as *reusable* lemmas (graph-free panel geometry, axiom-clean)
  and likely re-enter at the **Phase-23 general-`d`** join↔meet duality — but they are **off the
  `d=3` live route**. The three selector recasts (`hsel₁/₂/₃`) survive (they consume `r̂(Cᵢ)≠0`, which
  the producer still produces) — but see (e): the producer must now *prove* `r̂(Cᵢ)≠0` from the
  existential rather than receive it from the disjunction.
- **NB — `case_III_eq629_conditional` is also obsolete on the live route.** It mapped the three-fixed
  disjunction through `hselᵢ`; under the existential conclusion it has nothing to map (the producer
  consumes the existential directly). It has no code callers (the producer uses `case_III_claim612`
  directly, the C3 decision) — leave it as a reusable lemma or delete; not load-bearing for `d=3`.

**(d) The producer ripple — exact.** Only two code sites touch `case_III_claim612`:
`case_III_eq629_conditional` (RigidityMatrix.lean:1809, `.imp`) and `case_III_hsplit_producer`
(CaseI.lean:3688, `rcases`). No other callers (grep-confirmed; the rest are doc-comment mentions).
Under the existential restate:
- `case_III_eq629_conditional`: its premise list drops `hduality`/`C₁C₂C₃`; its body can no longer be
  `.imp hsel₁ …`. Either restate it to the existential-consuming shape or drop it (no callers). **Drop**
  is cleanest (it is pure glue, below the blueprint-node bar already — it has its own node
  `lem:case-III-eq629-conditional`, which should be folded into `lem:case-III-claim612`'s prose).
- `case_III_hsplit_producer`: drops `hduality`/`C₁C₂C₃`/the three-fixed `hmemᵢ`/`hcardᵢ`/`hselᵢ` keyed
  to fixed seeds; its body becomes `obtain ⟨q, hq⟩ := case_III_claim612 hr hp` then **build the
  candidate at the join `q`'s line** and feed C2. This is the genuine C5c-(2) producer restructure,
  unchanged in difficulty from §1.38 (the line-indexed candidate family) — but now the producer owns
  the *whole* selection (pick the join, build the matching candidate), not "receive a disjunct + run a
  pre-built selector."

**(e) The producer's real obligation, restated for the build phase.** Given the witness join `q`
(a pair `(i,j)` with `r̂(pᵢ∨pⱼ) ≠ 0`), the line `L = p̄ᵢ p̄ⱼ` lies in one of the three panels
`Π(a)/Π(b)/Π(c)` (incidence tabulation). The producer:
1. builds the eq.-(6.12) degenerate candidate placement (`case_II_placement_eq612`-style) **at line
   `L`** — i.e. with `v`'s normal sheared so the `va`-hinge's panel-meet is `C(L) = pᵢ∨pⱼ`;
2. its `(D−1)` panel rows span `(span C(L))^⊥` (the existing `span_panelRow_comp_single_of_edge` /
   `linearIndependent_sumElim_candidateRow_iff` machinery, now at line `L` rather than a fixed edge);
3. the row-space criterion at `C(L)` reads `r̂(C(L)) = r̂(pᵢ∨pⱼ) ≠ 0` ⟹ the candidate family is
   independent;
4. feed that family to C2 at the fixed placement.
This is the line-indexed candidate construction. The four points `p` the producer supplies to
`case_III_claim612` are chosen so their six joins are exactly the candidate lines KT's three placements
can realize — KT's `p₀ = Π(a)∩Π(b)∩Π(c)`, `p₁ ∈ Π(a)∩Π(b)∖Π(c)`, etc. (the N3a incidence pattern), so
*every* join lies in a panel the producer can split along.

**(f) Verdict on the coordinator's two questions.**
- *(a) Cleanest existential conclusion:* the `∃ q : six joins, r̂(join q) ≠ 0` form above (ranging over
  the six joins, NOT the full line continuum, NOT an `∃ (panel u, normal m)` form). It is (i) directly
  provable from `hr` + `span_omitTwoExtensor_eq_top` + `eq_zero_of_annihilates_span_top` (verified), and
  (ii) consumable: the producer picks the join, identifies its line `L = pᵢpⱼ ⊂ Π(u)`, builds the
  candidate at `L`, and the row-space criterion gives full rank.
- *(b) Does `hduality`/`hann` vanish entirely?* **Yes, completely.** No residual premise survives on
  `case_III_claim612`. `hann` was only ever the internal `by_contra` negation.

**Why existential over §1.38's B1 (carry `hann`).** B1 keeps `case_III_claim612` provable but (i)
leaves a *false-shaped* three-fixed disjunction as the conclusion the producer can't actually feed
without the same re-parameterization, (ii) keeps the obsolete C5c assembly on the live route as the
`hann`-discharging body, and (iii) carries `hann` (an abstract-panel premise over hardcoded N3a
normals) as producer data with no honest derivation — re-introducing the very honesty-gate problem at
the producer. The existential is faithful to KT (Claim 6.12 IS "∃ line choice, block full rank"),
matches what the producer must do anyway, and is a 5-line proof. The producer-internal restructure
(C5c-(2)) is identical in difficulty under both; the existential just removes the dead `hann` scaffolding.

**Leaf sequence (3–5 commits, dependency-ordered) — the buildable plan.**
1. **Leaf 1 (safe, local, buildable-now) — `case_III_claim612` existential restate.** Replace the
   three-fixed-`Cᵢ` + `hduality` signature with the existential conclusion (no premise); body = the
   5-line contrapositive verified above. Ripple the two callers: drop `hduality`/`C₁C₂C₃` from
   `case_III_eq629_conditional` (or delete it — no callers; fold its node into `lem:case-III-claim612`)
   and from `case_III_hsplit_producer`'s signature, leaving `case_III_hsplit_producer`'s body
   green-modulo (it now `obtain`s the witness join and carries the candidate-at-line construction as a
   new explicit hypothesis to discharge in Leaf 2–3). Reconcile `lem:case-III-claim612`'s blueprint
   prose to the existential (see *Blueprint*). **Graph-free** (no §38 trap): `case_III_claim612` is
   pure `Fin 4` / `ScrewSpace 2` geometry. One green unit.
2. **Leaf 2 — the line-indexed candidate placement.** Generalize `case_II_placement_eq612`'s seed/shear
   construction to take an **arbitrary witness line** (the join `pᵢ∨pⱼ`'s line `L ⊂ Π(u)`) rather than
   the implicit fixed `va`/`vb`/`ac`, producing the candidate framework whose `va`-hinge support is
   `C(L)` and its `(D−1)` block rows spanning `(span C(L))^⊥`. **Hits the §38 `ofNormals` trap** (it
   instantiates the concrete `ofNormals G ends q₀` carrier) — keep the row-space/independence reasoning
   over abstract `F` and instantiate only at the seed, per the existing C1/C2 discipline. Likely splits
   (the seed-from-line construction; the per-line block-failure / span criterion). Multi-commit.
3. **Leaf 3 — wire the producer.** `case_III_hsplit_producer`: `obtain ⟨q, hq⟩ := case_III_claim612 hr
   hp`; from `q` extract the line `L`, run Leaf 2 to build the candidate, run the row-space criterion at
   `C(L)` with `hq : r̂(pᵢ∨pⱼ) ≠ 0` to get the independent family, feed C2. Supplies the four points `p`
   adapted to the real panels (N3a-pattern, or directly from the framework's three candidate-panel
   normals). **§38 trap** at the C2 feed (the concrete carrier). Discharges the Leaf-1 green-modulo
   hypothesis. The C5c-(ii) OLD/NEW-block `hmemᵢ` work (independent, the `+1`-row `hmemᵢ` already in
   hand via `hingeRow_mem_rigidityRows`) rides alongside.
4. **Leaf 4 — `theorem_55` `d=3`-instance node (B.2)** — once the producer is green: instantiate
   `theorem_55 (n:=2) (k:=2)` on the three green branch args; mint the small green blueprint node.
   Graph-free (an instantiation). Then **Leaf 5 — the `lem:case-II-realization`/`lem:case-III` flips +
   Thm 5.5→5.6 push** feeding `rigidityMatrix_prop11`'s `hgen`, unblocking Cor 5.7 at `d=3`.

**Blueprint.** `lem:case-III-claim612`'s prose (case-iii.tex:1086–1134) currently describes the *carry-
`hduality`-as-explicit-hypothesis* model (1124–1133: "carries the union-(6.45) annihilation as an
explicit hypothesis `hduality`"). Under the existential restate that paragraph is wrong — the Lean no
longer carries `hduality`; the union annihilation is the internal `by_contra` negation. Rewrite the
final paragraph to: "the Lean `case_III_claim612` concludes the **existential** `∃ join, r̂(join) ≠ 0`
(the six joins of the four affinely-independent points), proved by contrapositive — if `r̂` annihilated
all six it would annihilate their span `= ⋀²ℝ⁴` (Lemma 2.1) and be zero. No `hduality` premise." The
statement-level prose (1095–1101) already reads as "at least one block full rank for some line choice" —
the existential — so only the formalization-aside paragraph changes. Reconcile in Leaf 1.

Built once, reused by all cases. **Green** unless marked.

| Brick | Lean name (`AlgebraicInduction.lean` unless noted) | Status | Reused by |
|---|---|---|---|
| Genericity device (Claim 6.4/6.9) | `exists_good_realization`, `_const`, `_ofParam` (`:2604`,`:3388`,`:2672`) | GREEN | Case I, Case II/III, Prop 1.1 |
| B0 row coordinatization (polynomial-in-normals) | `exists_good_realization_ofParam` (`:2672`) | GREEN | Case I, Case II/III |
| Device→motive closure (N7a) | `hasFullRankRealization_of_independent_panelRow` (`:2808`) | GREEN | all producers |
| N7b-0 (rigid-on-V ⟹ full-size independent panel-row subfamily) | `BodyHingeFramework.exists_independent_panelRow_subfamily_of_rigidOn` (`:2929`) | GREEN | Case I, Case II/III |
| N7b-1/2/3 (per-edge new-block rows; transport; pin-a-body column split) | `exists_independent_panelRow_subfamily_of_edge`, `…_transport`, `linearIndependent_sum_pinned_block` | GREEN | Case II/III (eq. 6.12) |
| Case-I splice glue (block-triangular gluing, genericity-free) | `BodyHingeFramework.isInfinitesimallyRigidOn_of_splice` (`lem:case-I-splice-seed`), `isInfinitesimallyRigidOn_union_of_inter` | GREEN | Case I |
| Splice producer (composes glue→N7b-0→device) | `hasFullRankRealization_of_splice` / `…_ofNormals` / `…_ofParam` | GREEN | Case I |
| Splice producer, general-position-free (N6a) | `hasFullRankRealization_of_splice_of_supportExtensor` / `…_of_supportExtensor_ofNormals` | GREEN — takes `hsupp` not `hgp`; non-simple Lemma 6.2 | Case I (non-simple) |
| Single-leg seed→realization bridge | `hasFullRankRealization_of_rigidOn_seed` (`:3151`) | GREEN | Case I, Case II/III |
| IH repackage (motive ⟹ rigid `ofNormals` locus) | `exists_rigidOn_ofNormals_of_hasFullRankRealization` (`:3192`) | GREEN (re-types under §1.3.5) | Case I |
| Per-leg rank polynomial (rigid leg ⟹ nonzero Gram-det `MvPolynomial`) | `exists_rankPolynomial_of_rigidOn` (`:3226`) | GREEN — **but needs `hne` (G1)** | Case I |
| Rank-polynomial consumer (non-root ⟹ rigid at that point) | `isInfinitesimallyRigidOn_ofNormals_of_rankPolynomial_ne_zero` (`:3315`) | GREEN | Case I |
| Constructive rank-witnessing mirror | `exists_polynomial_ne_zero_of_linearIndependent_at` (`Mathlib/LinearAlgebra/Matrix/Rank.lean`) | GREEN | Case I |
| General-position witnesses (moment curve) | `momentCurve`, `withMomentNormals`, `ofParam`, `isGeneralPosition_ofParam` (`:1785`–`:1933`) | GREEN | all (seed) |
| transversal hinge ⟹ nonzero extensor | `supportExtensor_ne_zero_of_isGeneralPosition` (`:1773`) | GREEN | all |
| N4 graph↔matroid contraction-minimality | `Graph.rigidContract_isMinimalKDof` (`Induction.lean`) | GREEN | Case I (`hcontract` recursion) |
| Count bridges (`V(G)`-relative N1–N3) | `finrank_pinnedMotionsOn_vertexSet`, `exists_relative_full_count_ofParam`, `isInfinitesimallyRigidOn_vertexSet_of_finrank_le` | GREEN | all |
| **Lemma 2.1 (extensor independence)** | `omitTwoExtensor_linearIndependent` (`Extensor.lean:493`) | GREEN — **hyp `AffineIndependent ℝ p`** | Case III (the missing row) |
| **(G2) general-position factor** | `exists_generalPosition_polynomial` (+ `pairLeadingMinorPoly`, `pair_linearIndependent_of_leading_minor_ne_zero`) | **GREEN** (2026-06-04; off-diagonal product of leading `2×2` minor polynomials) | Case I coupling |
| **Claim 6.4 collapse transport (G3a, superseded)** | `PanelHingeFramework.rigidContract_rigidity_transport` | **GREEN-MODULO** (2026-06-05; the motion-space `∃`-seed form of Claim 6.4 / eq. (6.9), carried as `htransport`; superseded by the block-triangular reframe — kept as a library brick) | (none; superseded) |
| **Claim 6.4 rank transport (N-22b-1)** | `PanelHingeFramework.rigidContract_exterior_rank_transport` (`CaseI.lean`) | **GREEN-MODULO** (2026-06-05; the §1.16 exterior-projected-row form of Claim 6.4 / eq. (6.9), carries `htransport` = the single-placement projected surviving-row independence; feeds N-22b-2 packaging; axiom-clean, no `sorry`) | Case I composer (N-22b-3 wire-up) |
| **Claim 6.4 packaging (N-22b-2)** | `PanelHingeFramework.exists_rankPolynomial_of_rigidOn_linking_set_proj` (`CaseI.lean`) | GREEN (2026-06-05; the bounded `D∘panelRow` producer variant) | Case I composer (N-22b-3 wire-up) |
| **`prop:rigidity-matrix-prop11` `hub`** | carried as hypothesis (`:2527`) | RED (multi-commit, Phase-19 partition count) | Prop 1.1 only |

**Reading:** the entire device + witness-transfer + splice + count + N4
substrate is GREEN; **(G2) is now GREEN too** (2026-06-04,
`exists_generalPosition_polynomial`). The Case-I substrate is **almost** complete:
the **Case-I Claim-6.4 collapse transport** (G3a, `rigidContract_rigidity_transport`)
landed **GREEN-MODULO** 2026-06-05, carrying KT eq. (6.9) as the explicit
hypothesis `htransport` (the relabel-induced normal change makes it irreducible — the
linking-edge lever fails). The composer that consumes it (`case_I_realization`) was
briefly valid-but-VACUOUS (commit c1ef55a, false `hpinc`); the **§1.12 fix has now
landed** — the asymmetric coupling `hasGenericFullRankRealization_of_couple_asymm_ofNormals_set`
removes the contraction leg's rank-polynomial round-trip, deletes `hpinc`, and supplies
the contraction rigidity directly from the `∀`-over-GP-seeds conjunct `htransportGP`
(KT eq. (6.9)); the composer is now honest GREEN-MODULO the Claim-6.4-only bundle,
axiom-clean. The N6b/N6c couplings are an
assembly of green bricks *given both legs as `≤ G` rigid `ofNormals`*; G3a supplies the
second such leg's *rigidity* (modulo `htransport` = KT Claim 6.4), but the **symmetric**
body-set coupling cannot consume it without `hpinc` — hence the asymmetric replacement.
The remaining *missing* analytic content across the layer is the Case-I contraction
transport (G3a's `htransport`, re-entering via `lem:case-III` / 22b+) and the
**Case-III missing row** via Lemma 2.1 (Track B, 22b+). (G1) was not a missing brick
— it was the motive decision of §1, dissolved by the two-motive split.

---

### 1.40 The CaseI.lean producer-core recon + the line-realizability constructibility verdict — (B), with two carried obligations the producer's own data supplies (2026-06-09)

> **Build-free design pass.** Recons the `case_III_hsplit_producer` core (CaseI.lean:3638, the
> `hcand` discharge — Leaf 2/3) against the green Lean and KT §6.4.1 (pp. 678, 690–691). Verdict on
> the coordinator's CRUX question (is the line-indexed candidate placement constructible for an
> *arbitrary* one of the six witness joins, or does it need a non-degeneracy the existential /
> Case-III hypotheses may not supply): **(B) — constructible, needs non-degeneracy, and the
> producer's own construction supplies it** — with one genuine residual the build must own (the
> abstract-N3a ↔ real-placement reconciliation + the split-leg `ab`-transversality), flagged below.
> No `.lean` / `.tex` edits this pass.

**The core, read end-to-end.** `case_III_hsplit_producer` is the **bare** `hsplit` branch of the
two-motive `theorem_55` (PanelHinge.lean:1160, it produces `HasFullRankRealization`, consumes the
bare `_hsplit : HasFullRankRealization 2 (G.splitOff v a b e₀)` — **no** GP/nonparallel promise). Its
body is now `obtain ⟨q, hq⟩ := case_III_claim612 hr hp; exact hcand q hq` (§1.39, Leaf 1, green); the
whole producer math is carried in the single green-modulo hypothesis
`hcand : ∀ q : six joins, r̂(pᵢ∨pⱼ) ≠ 0 → HasFullRankRealization 2 G`. Discharging `hcand` is the
genuine deferred core (Leaf 2/3). `HasFullRankRealization 2 G := ∃ Q, Q.graph = G ∧ Q rigid on V(G)`
(PanelHinge.lean:979) is an **existential over realizations** — the producer is free to choose `Q`'s
panel normals; this is the freedom the construction turns on.

**(1) How the current FIXED-seed placement works (`case_II_placement_eq612`, CaseI.lean:2719).** From
the IH-extracted rigid `ofNormals Gv ends q` (rigid on `V(Gv) = V(G)∖{v}`, `ab`-hinge `e₀` transversal
`hgab : LinearIndependent ![n_a, n_b]`, `n_a := q(a,·)`, `n_b := q(b,·)`), it places body `v`'s normal
at the **shear** `n_a + t•n_b` (`t ≠ 0`, the eq.-(6.12) seed `q₀`), overriding only the fresh
`v ∉ V(Gv)` so the `Gv`-block is untouched and the IH rigidity transports
(`ofNormals_update_eq_withNormal` + `toBodyHinge_withNormal_infinitesimalMotions_eq`). It assembles
`D(|V|−1)−1` independent rigidity rows = the OLD block (`exists_independent_panelRow_subfamily_of_rigidOn_linking`
+ the `f=id`, `hrow=rfl` transport N7b-2) ⊕ the NEW block (`exists_independent_panelRow_subfamily_of_edge`
at `e_b = vb`), pin-split through `v`'s screw column (N7b-3). The `+1` candidate row (the
candidate-completion, `linearIndependent_sum_augment_candidateRow`) lifts it to `D(|V|−1)`, gated by
the **row-space criterion** `linearIndependent_sumElim_candidateRow_iff F e_a r̂` ⟺ `r̂(C(e_a)) ≠ 0`
(`mem_hingeRowBlock_iff`: the `D−1` `va`-block rows already span `(span C(e_a))^⊥`, so appending `r̂`
raises rank to `D` iff `r̂ ∉ (span C(e_a))^⊥`). The carrier built is `ofNormals G ends q₀` (`withGraph`
the §38 trap); the criterion needs `r̂(C(e_a)) ≠ 0` for `C(e_a) = F.supportExtensor e_a`.

**(2) THE LOAD-BEARING GEOMETRIC FACT — the candidate's `va`-line is fixed by the IH seed, not the
shear.** `e_a = (v,a)`'s two panel normals are `v`'s normal `n_a + t•n_b` and `a`'s normal `n_a`, so
its support is `panelSupportExtensor (n_a + t•n_b) n_a`. By `panelSupportExtensor_add_smul_left`
(PanelLayer.lean:251, green) this is `(-t)•panelSupportExtensor n_a n_b = (-t)•C(e₀)` — a **scalar
multiple of the `ab`-hinge extensor `C(e₀)`**, for *every* `t ≠ 0`. **The shear `t` only rescales the
extensor; it does NOT move the line.** So a single IH realization at seed `q` realizes exactly **one**
`va`-line `span{C(e₀)} ⊂ Π(a)` (the meet of bodies `a`'s and `b`'s real panels). Symmetrically `M₂`
(`vb`-split) realizes one line in `Π(b)`, `M₃` (`ac`-split, the `a↔v` iso) one in `Π(c)`. **The
producer's three candidates therefore test `r̂` at three FIXED extensors `C₁,C₂,C₃` — exactly the
three-fixed situation §1.38/§1.39 confirmed cannot force `r̂ = 0` (three `2`-extensors span ≤ 3 of
`⋀²ℝ⁴`'s 6 dims).** KT's "for any `L ⊂ Π(a)`" freedom is genuine line-variation; the Lean shear is
*not* it. This is why Claim 6.12 had to become the existential over the **six** joins (Lemma 2.1, full
span) rather than the three candidate extensors — re-confirmed at the placement-construction level.

**(3) §38 trap map.** The §38 `ofNormals`/`withGraph` defeq-timeout bites exactly the sub-terms that
instantiate the heavy `ofNormals G ends q₀` carrier: `F.supportExtensor e_a` / `e_b` (the `hane`/`hnewne`
extensor-nonzero facts, CaseI.lean:2815/2823, discharged via `toBodyHinge_supportExtensor` +
`ofNormals_ends`/`ofNormals_normal` rewrites — reuse verbatim), `F.panelRow ends i ∈ F.rigidityRows`
membership (`panelRow_mem_rigidityRows` + `IsSubgraph.isLink_iff`), and the final
`hasFullRankRealization_of_candidateSelector` C2 feed (CaseI.lean:2204, which fixes `ofNormals G ends q₀`).
Generic-helper extraction (TACTICS-QUIRKS §38): the row-space/independence reasoning is **already**
graph-free over abstract `F` (`linearIndependent_sum_{p2,p3,augment}_candidateRow[_selector]`,
`case_II_placement_eq612`'s blocks read only `ends`/`q₀`/`supportExtensor`); keep it abstract and
instantiate `ofNormals` only at the seed (the C1/C2/L1–L4 discipline, already followed). The one new
place the trap may newly bite is the per-line second-normal `n'` plumbing of (4) — but
`exists_independent_perp_pair` + the Leaf-2b core are pure `Fin 4` geometry (graph-free), so the trap
stays confined to the existing C2-feed site. No *new* generic helper is forced beyond what L3 already
anticipated (`panelRow_ofNormals_candidate_eq`, §1.34 L3) unless a `convert`/`rw` walls.

**(4) THE CRUX, settled — verdict (B).** The chain that closes the gap, every link verified green:
- The producer **supplies the four points `p`** to `case_III_claim612` (they are a *parameter*, not
  fixed) — so it uses the self-contained N3a witness `exists_affineIndependent_panel_incidence`
  (RigidityMatrix.lean:290, green): three nonparallel normals `n : Fin 3 → ℝ⁴` (`LinearIndependent`)
  + four affinely-independent points `p` with the `Π(a)/Π(b)/Π(c)` triple-intersection incidence.
- For the witness join `q`, the kept-pair identity `omitTwoExtensor_homogenize_eq_extensor_kept`
  (green) gives `pᵢ∨pⱼ = extensor ![p̄_c, p̄_d]`; the six-join dispatch
  `exists_hduality_witness_of_panel_incidence` (green, `2bd5fa2` — **obsolete on §1.39's `hann`-route
  but its `fin_cases q` panel-assignment is reusable**) shows **all six joins are covered**: the three
  through-`p0` joins lie in TWO panels (use two N3a normals), the three "opposite" joins in ONE panel
  (the second normal `n'` from `exists_independent_perp_pair`, RigidityMatrix.lean:377, green —
  rank–nullity: the common-perp of two points in `ℝ⁴` is `≥ 2`-dim, strictly above `span{n_u}`).
- The Leaf-2b core `panelSupportExtensor_add_smul_left_ne_zero_of_join_ne_zero` (PanelLayer.lean:332,
  green) is the keystone: given `n_u, n'` independent with both join points `⊥` both, and `t ≠ 0`,
  `r̂(extensor ![pi,pj]) ≠ 0 ⟹ r̂(panelSupportExtensor (n_u + t•n') n_u) ≠ 0` — i.e. the existential
  witness `r̂(pᵢ∨pⱼ) ≠ 0` forces `r̂(C(e_a)) ≠ 0` at the candidate built with `n_u`/`n'`, the exact
  row-space-criterion input. The `-t` cancels under `r̂` (the shear-invariance of (2), turned to
  advantage: the line is `n_u ∧ n'` regardless of `t`).
- **So the construction IS feasible for an arbitrary one of the six witnesses** — provided the
  candidate's `va`-hinge is built with `n_u, n'` = the witness join's two panel normals. **The
  non-degeneracy needed** — (i) the three panels nonparallel (`LinearIndependent n`), (ii) the four
  points affinely independent, (iii) per opposite join a transversal second normal `n'` — **is supplied
  by the producer's own data**: (i)/(ii) by N3a (self-contained, the producer constructs them), (iii)
  by `exists_independent_perp_pair`. None is a carried obligation that could be undischargeable for a
  specific witness; N3a covers all six uniformly. **Verdict (B):** non-degeneracy is needed and the
  producer's construction (not a fragile Case-III hypothesis) supplies it. This is *not* the `hann`-trap
  shape — there is no premise on a specific witness that could fail; the existential is fully consumed.

**(5) The two genuine residuals the build must own (why (B) not a clean "all six, nothing needed").**
The verdict is (B) and not (A) because two reconciliations are real producer-internal work, not free:
- **(R1) abstract-N3a ↔ real-placement panels.** The Leaf-2b core takes the candidate's *actual* `va`
  normals `n_u = n_a`, `n' = n_b` — the **real IH realization's** normals (`n_a = q(a,·)`,
  `n_b = q(b,·)`), read off `_hsplit`'s framework. The witness-join points `p̄_c, p̄_d` are the
  **abstract N3a** points, orthogonal to the **abstract N3a** normals `n : Fin 3 → ℝ⁴` — *not* a priori
  to the real `n_a, n_b`. The core fires only when `p̄_c, p̄_d ⊥ n_a, n_b`. So the build must **identify
  the N3a normals with the real candidate-panel normals** — either choose `p` relative to the real
  `n_a, n_b, n_c` (an N3a *parameterized by given nonparallel normals*, which the current
  `exists_affineIndependent_panel_incidence` does NOT expose — it constructs `n = e₀,e₁,e₂`), or build
  the candidate placement's normals to be the N3a `n`. The latter is available: `HasFullRankRealization`
  is existential, and `case_II_placement_eq612` reads `n_a, n_b` from the IH seed `q` — but `q` (the
  split-off realization) comes from `_hsplit`, fixed, so the producer cannot freely set `n_a, n_b` to
  the N3a normals without re-realizing the split-off graph. The honest resolution: generalize N3a to
  **take the real panel normals as input** (a points-from-given-normals existence lemma, via
  `exists_ne_zero_dotProduct_eq_zero` (green) per panel-intersection + the affine-independence
  det-polynomial route already green), so `p` is built against the real `n_a, n_b, n_c`. This is a new
  graph-free leaf, bounded (the det-polynomial machinery N3a uses is all green), but it IS new work —
  the current N3a is the wrong shape for the producer (it hardcodes the normals).
- **(R2) the split-leg `ab`-transversality.** `case_II_placement_eq612` needs
  `hgab : LinearIndependent ![n_a, n_b]` (the `ab`-hinge `e₀` transversal at the IH seed) and the three
  panels nonparallel (`LinearIndependent ![n_a, n_b, n_c]`) for the candidate lines to be genuine
  `(d−2)`-flats and the N3a identification (R1) to be non-degenerate. The **bare** `_hsplit` motive
  carries **no GP/nonparallel promise** (PanelHinge.lean:1160; the GP motive `hsplitGP` does, but
  `case_III_hsplit_producer` is the bare branch). This is the Track-B "incoming split-leg nonparallel"
  flag (§3 Track B; KT pp. 673–675's Claim-6.4 nonparallel input). KT obtains it from the IH's
  "nonparallel if simple" — i.e. the **GP motive**. So discharging `hcand` at full generality may need
  the producer to consume the GP `_hsplit` (route through `hsplitGP`/`HasGenericFullRankRealization`),
  or to supply the transversality some other way. This is the same general-position dependency Case-I's
  simple cases hit (G1, dissolved by the two-motive split); for Case III it re-surfaces as the question
  *which `theorem_55` branch the producer lives in*. **Flagged, not yet resolved:** confirm at Leaf-3
  build whether the bare branch suffices (e.g. transversality of the *specific* `ab`-hinge follows from
  `G.splitOff`'s structure + minimality without full GP) or whether `case_III_hsplit_producer` must be
  restated to consume the GP motive. This does NOT re-incur the `hann` trap (it is a motive-strength
  question, fully tracked by the two-motive split, not a smuggled hypothesis with no node).

**(6) Buildable-leaf decomposition of the CaseI.lean core (discharging `hcand`, Leaf 2/3).** Bottom-up,
each a smallest-buildable commit; the `[green]` bricks are already in tree:
1. **L2b-place — the line-indexed candidate placement.** Generalize `case_II_placement_eq612` /
   `case_III_old_new_blocks` (CaseI.lean:3353) to take the candidate's `va`-hinge normals as the
   witness panel's `n_u, n'` (rather than the implicit IH `n_a, n_b`): produce the candidate framework
   `ofNormals G ends q₀` whose `va`-support is `panelSupportExtensor (n_u + t•n') n_u = (-t)•C(L)` and
   whose `(D−1)` block rows span `(span C(L))^⊥`. Reuses the green OLD/NEW block infra (L1) + L2 span
   bridge + the shear lemmas `[green]`; the §38 trap is confined to the `ofNormals` carrier. Likely
   splits (the seed-from-line construction; the per-line block span at `C(L)`).
2. **N3a-from-normals (R1) — points adapted to the real panels.** A graph-free leaf:
   `∃ p, AffineIndependent p ∧ (the six-join incidence relative to the real nonparallel `n_a,n_b,n_c`)`,
   built via `exists_ne_zero_dotProduct_eq_zero` `[green]` per panel + the det-polynomial affine-indep
   route `exists_affineIndependent_of_det_polynomial_ne_zero` / `exists_detPolynomial_of_pointPolynomial`
   `[green]`. Replaces the hardcoded-normals `exists_affineIndependent_panel_incidence` for the producer.
3. **per-line block-failure / span criterion at `C(L)`** — run `linearIndependent_sumElim_candidateRow_iff`
   `[green]` at the L2b-place candidate's `e_a` with `r̂(C(L)) ≠ 0` (from the Leaf-2b core `[green]`,
   fed the witness `hq`) → the independent `D(|V|−1)`-family.
4. **row-space-criterion → C2 feed** — `hasFullRankRealization_of_candidateSelector` `[green]` (C2) at
   the fixed `ofNormals G ends q₀`, the per-row `rigidityRows` membership from L4
   `panelRow_mem_rigidityRows` `[green]`. Discharges `hcand q hq`. **§38 trap** at the carrier.
5. **(R2) motive-branch reconciliation** — confirm bare `_hsplit` suffices or restate to GP; the
   six-join panel dispatch reuses `exists_hduality_witness_of_panel_incidence`'s `fin_cases q`
   assignment `[green]` + `exists_independent_perp_pair` `[green]` for the second normals.

**Smallest next buildable sub-leaf:** **L2b-place** (item 1) — the line-indexed generalization of
`case_II_placement_eq612`'s seed/shear, the prerequisite all of 3/4 consume; its seed-from-line
*geometric* core already landed (`panelSupportExtensor_add_smul_left_ne_zero_of_join_ne_zero`, Leaf 2b
done). **Flag (R2) at Leaf 3** as the one genuine open architectural question (bare vs GP motive); it
does not block L2b-place. The reuse map for Phase 23 general-`d` (§1.33 (C)/(D)) is unchanged.

---

### 1.41 The R2 producer-signature verdict — (B): the `hsplit` producer must consume the GP `_hsplit`; the two-motive structure supplies it cleanly, the green Case-I precedent does exactly this, the Leaf-4 ripple is `theorem_55_generic` (2026-06-09)

> **Build-free design pass settling the §1.40 (R2) carried obligation** — the producer-signature
> crux the coordinator flagged as the one genuine open architectural question before L2b-place
> builds. Verdict: **(B) — needs the GP motive, and the two-motive structure provides it cleanly.**
> The producer is restated to live in `theorem_55_generic`'s `hsplitGP` branch (consuming the GP
> `_hsplit`); the **green precedent does precisely this** (`case_I_realization` *is* `hcontractGP`);
> the Leaf-4 ripple is "instantiate `theorem_55_generic`, not bare `theorem_55`", and the bare
> conclusion the capstone needs flows out via the `.2` conjunct for free. One bounded new sub-obligation
> falls out (R3 below): the producer must discharge the `(G.splitOff …).Simple` antecedent of the GP IH
> conjunct — KT Lemma 6.7(ii)'s triangle argument, *not yet formalized*, a sibling of Case I's green
> `rigidContract`-simplicity leaf. This refines (B) but does not make it (C). No `.lean`/`.tex` edits
> this pass. Verified against the green Lean (`theorem_55`/`theorem_55_generic` PanelHinge.lean:1098/
> 1154; `IsGeneralPosition` :121; `ofNormals_normal` :268, `rfl`; `HasFullRankRealization`/
> `HasGenericFullRankRealization` :979/:1033; `case_II_placement_eq612` CaseI.lean:2719;
> `case_I_realization` :1999; `case_III_hsplit_producer` :3638) and KT pp. 669/677–678/680–682.

**(1) Exactly what the placement requires, and that the bare motive does NOT promise it.**
`case_II_placement_eq612` (CaseI.lean:2719) and its block-front `case_III_old_new_blocks` (:3353)
take, as an explicit hypothesis, only the **pair** transversal
`hgab : LinearIndependent ![q(a,·), q(b,·)]` (the IH seed's `ab`-hinge `e₀`); it consumes it twice
(`hane` :2815, `hnewne` :2823 — the `va`-line `(-t)•C(e₀) ≠ 0` and the reproduced `vb`-row, both via
`panelSupportExtensor_ne_zero_iff … |>.mpr hgab`). It does **not** take the nonparallel *triple*
`![n_a,n_b,n_c]` — that enters only at the Claim-6.12 witness-points / N3a stage (R1, where the
points must be orthogonal to the three *real* panel normals). The producer `case_III_hsplit_producer`
(:3638) obtains the IH realization `q` and must *supply* `hgab`. Its `_hsplit` is the **bare**
`HasFullRankRealization 2 (G.splitOff v a b e₀)` (:3645), which by definition (PanelHinge.lean:979)
is only `∃ Q, Q.graph = G' ∧ Q.toBodyHinge.IsInfinitesimallyRigidOn V(G')` — **no panel-normal
linear-independence promise**. So the bare branch cannot hand the producer `hgab`. **(A) is refuted:**
no structural fact of a rigid `ofNormals` realization forces `ab`-hinge transversality (a rigid
realization can have a parallel-panel pair — that is exactly the non-simple regime KT's Lemma 6.2
inhabits, where parallel panels are *wanted*).

**(2) The GP motive supplies `hgab` by definition.** `IsGeneralPosition P := ∀ a b, a ≠ b →
LinearIndependent ![P.normal a, P.normal b]` (PanelHinge.lean:121). For `P = ofNormals Gv ends q`,
`P.normal a = fun i => q (a, i)` *by `rfl`* (`ofNormals_normal` :268). So a GP realization's
`IsGeneralPosition` conjunct, applied at `a ≠ b`, is **definitionally** `hgab : LinearIndependent
![q(a,·), q(b,·)]`. The match is exact — no bridge lemma. `HasGenericFullRankRealization` (:1033)
carries that `Q.IsGeneralPosition` conjunct; the bare `HasFullRankRealization` does not. **This is
the lemma/structural fact (B) names: `IsGeneralPosition` IS the `hgab` transversal.**

**(3) The green precedent — `case_I_realization` extracts the same transversal from the GP IH, and
it lives in `hcontractGP`.** `case_I_realization` (:1999) concludes
`HasGenericFullRankRealization k G`, takes the **conditioned (GP) IH** `hIH : ∀ G', … → (G'.Simple →
HasGenericFullRankRealization k G') ∧ HasFullRankRealization k G'`, requires `hSimple : G.Simple`,
and pulls each leg's general-position realization from the *GP* conjunct of that IH
(`obtain ⟨QH, hQHg, hQHgp, …⟩ := (hIH H …).1 (hSimple.mono hle)`, :2056 — `hQHgp : QH.IsGeneralPosition`
is precisely the transversality source). The doc-comment (CaseI.lean:153) states it outright: this
node *is* `theorem_55_generic`'s `hcontractGP`. So in the **already-green** precedent, the
general-position / transversality inputs come from the **GP IH motive** — exactly the route Case III
should mirror. This is the cheapest correct route and it directly answers R2: **Case III's `hgab`
comes from the GP `_hsplit`, the same place Case I's leg transversals come from.**

**(4) KT cross-check — the transversality rests on simplicity + the "nonparallel if simple" IH, i.e.
the GP motive.** KT §6.4.1 (pp. 680, 682, Lemma 6.10) opens its `q`-extraction with: *"by (6.1),
there exists a **generic nonparallel** panel-hinge realization `(G_v^{ab}, q)`"* — explicitly
nonparallel (= general position). The nonparallel property is what makes `Π(a),Π(b),Π(c)` pairwise
transversal and lets eq. (6.12)'s `L ⊂ Π(a)` be a genuine `(d−2)`-flat; p. 682 closes on *"if the
configuration of these three panels is **generic**, the extensors span 6 dims."* That nonparallel IH
rests on two facts KT pins first: **`G_v^{ab}` is simple** (Lemma 6.7(ii): a degree-2 split of a
2-edge-connected no-proper-rigid-subgraph graph is simple — else a triangle `{va,vb,ab}` is a proper
rigid subgraph), and **the standing inductive choice that simple graphs get a nonparallel (generic)
realization** (§5.1 / Lemma 5.2's perturbation, the algebraically-independent-coordinates choice of
footnote 6). KT obtains the transversality from *exactly* the data the GP motive carries
(`IsGeneralPosition` + the alg-independence conjunct), conditioned on simplicity — **the formal
two-motive split is a faithful transcription of KT's "nonparallel, if simple"** (p. 669). The bare
motive is the right one only at the non-simple leaves (Lemma 6.2, parallel panels *wanted*), where no
`hgab` is needed because Case III does not fire there (no degree-2 reducible vertex in the parallel-K₂
base).

**(5) The route — restate the producer to `hsplitGP`, and the Leaf-4 ripple.** The producer is
restated to the `theorem_55_generic.hsplitGP` shape (PanelHinge.lean:1167): it gains `G.Simple` and
the *conditioned* IH `((G.splitOff …).Simple → HasGenericFullRankRealization 2 (G.splitOff …)) ∧
HasFullRankRealization 2 (G.splitOff …)`, and concludes `HasGenericFullRankRealization 2 G`. It pulls
`q` (with `hgab` = the `IsGeneralPosition` conjunct) from the GP `_hsplit` via the IH's `.1`
conjunct, **after discharging the `(G.splitOff …).Simple` antecedent of that conjunct (R3, below).**
The **Leaf-4 ripple** (was: instantiate bare
`theorem_55 (n:=2)(k:=2)`, §1.33 (B.2)/(E)) becomes: instantiate **`theorem_55_generic (n:=2)(k:=2)`**
on the six green/green-modulo branch args (`hbase`, `hbaseGP`, `hsplit`, **`hsplitGP`** = the restated
Case-III producer, `hcontract`, `hcontractGP` = `case_I_realization`), and read the **bare**
`HasFullRankRealization 2 G` the capstone needs off the conclusion's **`.2` conjunct**
(`(theorem_55_generic … G …).2`). The skeleton at PanelHinge.lean:1191–1206 already threads exactly
this — base/split/contract each return the `⟨GP-if-simple, bare⟩` pair, with `hsplit`'s bare half fed
`hIH.2`. So the ripple is *absorbed by the existing skeleton*: Leaf 4 mints a small green
`theorem_55_generic (n:=2)(k:=2)` instance node (still **not** a standalone `theorem_55_dim3`; the
general node stays red-pending-Phase-23) and projects `.2`. The terminal consumer
`rigidityMatrix_prop11`'s `hgen` (PanelHinge.lean:1247) needs only a `finrank` rank lower bound, which
the bare `.2` motive supplies through the Thm 5.5→5.6 push — **the GP motive never reaches the
capstone; it is purely internal scaffolding for the simple-case induction.**

**(6) The third carried obligation R3 — the `(G.splitOff …).Simple` side-condition is a bounded
to-build leaf, NOT green.** Discharging the GP `_hsplit` from the conditioned IH's `.1` conjunct
requires proving its antecedent `(G.splitOff …).Simple`. The `hsplit`/`hsplitGP` branch hands the
producer `hG : G.IsMinimalKDof n 0`, `hnoRigid : ∀ H, ¬ IsProperRigidSubgraph`, the degree-2 data,
and (in `hsplitGP`) `G.Simple` — but **not** `(G.splitOff …).Simple` (verified: `minimal_kdof_reduction`
hands it down at ForestSurgery.lean:996–1000; no `splitOff`-simplicity fact is in tree, and
PanelHinge.lean:995 explicitly notes `splitOff` does *not* preserve simplicity in general). KT Lemma
6.7(ii) (p. 677) is exactly this fact — `G_v^{ab}` is simple for a degree-2 split of a
2-edge-connected minimal `0`-dof-graph with no proper rigid subgraph (else the triangle `{va,vb,ab}`
is a proper rigid subgraph, contradicting `hnoRigid`). It is **bounded** (the contradiction-via-triangle
argument from `hnoRigid`), but it is **not formalized** — and 2-edge-connectivity (its other input) is
not yet a project notion. So R3 is a new graph-side leaf, the exact sibling of Case I's green
`rigidContract_isSimple_of_isProperRigidSubgraph` (Contraction.lean:151, which derives
`(G.rigidContract H r).Simple` from `H.IsProperRigidSubgraph G n` + `G.Simple`).

**Why this is (B) not (C).** R3 does NOT downgrade the verdict: (C) is reserved for "the GP `_hsplit`
is *not cleanly available* at `d=3`" or "the Leaf-4 ripple is *nontrivial*". Neither holds — the GP
`_hsplit` is available *given* R3's bounded side-condition (a triangle-contradiction lemma, not a
research obstacle), and the Leaf-4 ripple is fully absorbed by the existing two-motive skeleton
(:1191–1206 already threads the `⟨GP-if-simple, bare⟩` pair and feeds `hsplit` the `hIH.2` bare half;
the capstone reads the bare `.2`). The cost of (B) over a hypothetical (A) is: one signature change
(`case_III_hsplit_producer` gains `G.Simple` + the conditioned IH, concludes GP) + the R1 work
(tracked) + the R3 simplicity leaf (bounded, new). **This does not re-incur any honesty-gate problem:**
the motive strength is fully tracked by the two-motive split (the device that dissolved Case-I's (G1)
gap), and R3 is a visible graph-side obligation with a clear KT source, not a smuggled hypothesis.

**Net effect on the build:** L2b-place is unaffected (it reasons over abstract `F` and takes the
candidate normals as inputs — the motive question is upstream of it). The R2 verdict re-shapes **Leaf
3** (the producer signature: `G.Simple` + conditioned IH, GP conclusion, `hgab` from the GP conjunct,
+ the R3 simplicity discharge) and **Leaf 4** (instantiate `theorem_55_generic`, project `.2`). Both
are bounded restatements against an existing two-motive skeleton, plus the bounded R3 leaf — not new
*hard* math. The producer's own N3a + perp-pair (R1) still supply the *triple* nonparallel for the
witness-points; the GP motive supplies the *pair* `hgab` for the placement seed; R3 supplies the
simplicity that unlocks the GP conjunct — all three now have a home.

---

### 1.42 The two remaining general-position residuals settled — R1-affine verdict (A) (dissolves: the consumers are homogeneous-vector-native, affineness was a vestige) + R3 verdict (A) (clean triangle mirror, bounded, no 2-edge-connectivity needed in the proof) (2026-06-09)

> **Build-free design pass settling the producer's two GENERAL-POSITION residuals before the Leaf-3
> build consumes them** — R1-affine (the affine de-homogenization the §1.40 R1 split off as "the
> genericity-bearing residual") and R3 (splitOff-simplicity, the §1.41 carried obligation flagged as
> "bounded but 2-edge-connectivity isn't a project notion"). Both verdicts: **closes, genericity-free
> / bounded — the Leaf-3 producer is genuinely buildable.** Verified against the green Lean
> (`omitTwoExtensor_linearIndependent` Extensor.lean:493 — proof uses only the LI hypothesis, the
> `homogenize` bridge at :498–500 is the only affine touchpoint, confirmed by a `lean_multi_attempt`
> generalization that *closes* with bare `LinearIndependent ℝ v`; `span_omitTwoExtensor_eq_top`
> RigidityMatrix.lean:124; `case_III_claim612` :1719; `exists_homogeneousIncidence_of_normals` :452;
> `panelSupportExtensor_add_smul_left_ne_zero_of_join_ne_zero` PanelLayer.lean:332 — takes bare
> `pi pj : Fin 4 → ℝ` with `⬝ᵥ`-orthogonality, NOT `homogenize` of affine points; `IsGeneralPosition`
> PanelHinge.lean:121 — *pairwise* only; `theorem_55_generic.hsplitGP` :1167; `splitOff` Operations.lean:574;
> `rigidContract_simple` Contraction.lean:144) and **KT Lemma 6.7(ii)** (p. 677, read in full from the
> 2011 DCG PDF). No `.lean`/`.tex` edits this pass.

**R1-affine — verdict (A): it DISSOLVES; the producer chain is homogeneous-vector-native and
affineness was a vestigial signature, not a requirement.** The §1.40 split called the affine
de-homogenization "the genericity residual — an orthogonal vector can lie at infinity." It is a real
geometric danger *for the de-homogenization map itself* — but the de-homogenization is **not needed**.

- *The at-infinity danger is real if you de-homogenize.* A homogeneous `pbar : Fin 4 → ℝ⁴` represents
  a finite affine point iff a scalar multiple has last coordinate `1`, i.e. iff `pbar (Fin.last 3) ≠ 0`
  (`homogenize p = Fin.snoc p 1`, Extensor.lean:110); it is *at infinity* iff `pbar (last) = 0`. The
  homogeneous core's triple-intersection point `pbar 0` is the common perp of `n_a, n_b, n_c`; its last
  coordinate is `0` **iff** `e₃ = (0,0,0,1) ∈ span{n_a,n_b,n_c}` (the common perp lies in the
  at-infinity hyperplane `H_∞ = {e₃}^⊥` iff `H_∞ ⊇ {n}^⊥` iff `e₃ ∈ span{n}`). For LI normals this is a
  genuine codimension-1 possibility that `LinearIndependent ℝ n` does **not** exclude — so a naive
  "rescale each `pbar i` to last-coord 1" lemma is genuinely false for some real normals. This is the
  GP-residual the §1.40 R1 split smelled.
- *But the consumers never need affineness — only LI of the four homogeneous vectors.* The two consumers
  the producer feeds — `span_omitTwoExtensor_eq_top` (N1) and its contrapositive `case_III_claim612` —
  bottom out on **Lemma 2.1** (`omitTwoExtensor_linearIndependent`). Reading its proof
  (Extensor.lean:493–538): it `set v := fun i => homogenize (p i)`, derives `hv : LinearIndependent ℝ v`
  *once* (:498–500, the only use of `AffineIndependent`/the homogenization), and the **entire rest of the
  proof uses only `hv`** — every supporting brick (`join_pair_omitTwo_self_ne_zero`,
  `join_pair_omitTwo_other_eq_zero`) takes a bare `v : Fin (e+2) → Fin (e+2) → ℝ` + `LinearIndependent`.
  A `lean_multi_attempt` of the generalized statement `omitTwoExtensor_linearIndependent_of_li (v)
  (hv : LinearIndependent ℝ v)` with that body verbatim **closes (`goals:[]`)**. So the six omit-two
  joins of *any* LI `Fin 4 → ℝ⁴` family span `⋀²ℝ⁴ = ScrewSpace 2` — affineness is irrelevant to N1/N2.
- *And the seed-from-line bridge is already homogeneous-native.* The Leaf-2b core
  `panelSupportExtensor_add_smul_left_ne_zero_of_join_ne_zero` (PanelLayer.lean:332) and its unsheared
  transfer (:303) take the join points as bare `pi pj : Fin 4 → ℝ` with **`⬝ᵥ`-orthogonality**
  `pi ⬝ᵥ n_u = 0 ∧ pi ⬝ᵥ n' = 0` (etc.) — *not* `homogenize` of affine `ℝ³` points. The incidence the
  build actually consumes is "the join's two homogeneous vectors are dot-orthogonal to the two real
  candidate normals", which is **exactly what the homogeneous core `exists_homogeneousIncidence_of_normals`
  delivers, relative to the real `n_a,n_b,n_c`** (:455–458, the `pbar i ⬝ᵥ n u` pattern). Nothing
  downstream reads a last coordinate or an `ℝ³` point.
- *The clean route.* Restate the two consumers to the **homogeneous-vector layer**: take a bare
  `pbar : Fin 4 → Fin 4 → ℝ` with `hpbar : LinearIndependent ℝ pbar` (replacing
  `{p : Fin 4 → Fin 3 → ℝ} (hp : AffineIndependent ℝ p)` and `omitTwoExtensor (homogenize ∘ p)` with
  `omitTwoExtensor pbar`), backed by the new `omitTwoExtensor_linearIndependent_of_li` (the
  affine-free Lemma 2.1, the verbatim-body generalization above). The producer then feeds
  `exists_homogeneousIncidence_of_normals hn` (whose `hn : LinearIndependent ℝ n` is the GP triple — see
  the R2/R3 note: the GP `_hsplit` supplies *pairwise*, the *triple* `LinearIndependent ![n_a,n_b,n_c]`
  is the producer's own N3a-shaped construction, NOT GP, and the homogeneous core already takes it as
  input) **directly**: its LI `pbar` + the eq.-(6.45) incidence relative to the real `n` are the exact
  inputs. **No de-homogenization, no `homogenize`-rescaling lemma, no at-infinity case, no genericity.**
  The current affine signature is a vestige inherited from before the homogeneous core landed.
- *Why (A) not (B).* (B) would be "needs general position of the real normals and the GP motive supplies
  it"; (C) "the GP guarantee is too weak / per-witness affine-realizability fails". **Neither holds: the
  finiteness/affineness was never needed.** There is no per-witness failure (the hann-trap shape the
  coordinator flagged) because there is no per-witness affine-realizability obligation at all — the
  existential is fully consumed at the homogeneous-vector layer. The danger the §1.40 split identified
  is real but routed around, not incurred: it lives only in the de-homogenization map, which the build
  simply does not call. **R1's homogeneous core (already green) is the whole of R1; R1-affine is empty.**

**R3 — verdict (A): clean triangle mirror of the green Case-I simplicity leaf, bounded; the proof
does NOT need 2-edge-connectivity.** The §1.41 R3 flag held two facts in apparent tension —
"2-edge-connectivity isn't a project notion" and "a sibling of Case I's green `rigidContract`-simplicity
leaf, bounded". Reading **KT Lemma 6.7(ii)'s actual proof** (p. 677, verbatim) resolves it cleanly:

> *"If `G_v^{ab}` is not simple, then `G_v^{ab}` contains two parallel edges between `a` and `b`
> (because the original graph `G` is simple). This implies `ab ∈ E`. Therefore `G` contains a triangle
> `G[{va,vb,ab}]` as its subgraph. Since a triangle is a 0-dof-graph, `G` contains a proper rigid
> subgraph, contradicting the lemma assumption."*

- *What the proof rests on, exactly:* (i) `G.Simple` — supplied by `hsplitGP` (PanelHinge.lean:1171);
  (ii) `splitOff`'s only new edge is `e₀ = ab` and `e₀ ∉ E(G)` is given (`_he₀`), so a parallel edge in
  `G_v^{ab}` to `e₀` forces a *pre-existing* `G`-edge `ab` (`splitOff_isLink`, Operations.lean:614 — the
  surviving edges are exactly the `e₀`-distinct `v`-avoiding edges of `G`); (iii) the triangle
  `{va, vb, ab}` is then a subgraph of `G` (`va = eₐ`, `vb = e_b`, `ab` the supposed pre-existing edge),
  it is a proper subgraph because `|V(G)| ≥ 4` in the splitting branch (`{v,a,b} ⊊ V(G)`), and a triangle
  is a 0-dof-graph hence rigid — contradicting `hnoRigid` (`_hnoRigid : ∀ H, ¬ H.IsProperRigidSubgraph
  G n`, supplied). **The proof of (ii) does not use 2-edge-connectivity.** 2-edge-connectivity is a
  *standing* hypothesis of KT §6.4 used *elsewhere* (Lemma 4.6, to *find* the degree-2 vertex — which
  the producer already receives as the `_hdeg2`/`_hG_ea`/`_hG_eb` data), not in the simplicity argument.
  So **R3 needs no 2-edge-connectivity notion** — the apparent tension was a mis-attribution of the
  section's standing assumption to the lemma's proof.
- *Loop-freeness (the other simplicity half):* `G_v^{ab}` simple also needs no `a`-`a` self-loop at
  `e₀`, i.e. `a ≠ b`; this follows from `eₐ ≠ e_b` + `G` simple + the degree-2 data (`a, b` are the two
  *distinct* neighbours of `v`; if `a = b` then `eₐ, e_b` are parallel `va`-edges, contradicting `G`
  simple). Bounded combinatorics off the supplied `_hG_ea`/`_hG_eb`/`_heab`/`G.Simple`.
- *The green sibling (corrected name — §1.41's pointer drifted).* §1.41(6) named the precedent
  `rigidContract_isSimple_of_isProperRigidSubgraph` (Contraction.lean:151); **that decl does not exist.**
  The actual green Case-I simplicity leaf is **`rigidContract_simple`** (Contraction.lean:144), which
  derives `(G.rigidContract H r).Simple` from realized-graph `hloop`/`hpar` hypotheses; the G2c step of
  `case_I_realization`'s composer discharges those from `H.IsProperRigidSubgraph G n` + `G.Simple`. R3 is
  the same shape: derive `(G.splitOff …).Simple` (no surviving edge collapses to a loop or a parallel
  pair) from `G.Simple` + `hnoRigid` + the split structure, via the triangle contradiction. A new
  graph-side leaf in `Operations.lean` (a `splitOff_simple_of_…` sibling of `rigidContract_simple`),
  bounded — the only non-routine ingredient is "a triangle is a 0-dof-graph / proper rigid subgraph",
  which is the same triangle-is-rigid fact KT's Lemma 4.6/6.7 family uses and which the project's
  `IsProperRigidSubgraph` + 0-dof machinery (Phase 19/20) can state directly.
- *Why (A) not (B)/(C).* (C) is reserved for "needs an unformalized notion (2-edge-connectivity etc.)";
  the proof needs none. (B) "needs more than the mirror but the pieces are green"; the mirror *is* the
  argument (triangle-contradiction off `hnoRigid`, exactly as Case I's leaf is a `map`-simplicity
  contradiction off `IsProperRigidSubgraph`). It is **new** Lean (not green — `splitOff` simplicity is
  nowhere in tree, and PanelHinge.lean:995 explicitly notes `splitOff` does not preserve simplicity in
  general, which is *why* it must be conditioned on `hnoRigid`), but it is the clean bounded mirror, so
  the honest verdict is (A) on the "clean mirror, bounded" axis with the standing caveat that it is a
  to-build leaf, not a green one.

**Combined buildability conclusion.** Given the GP-motive data the producer consumes (the
`theorem_55_generic.hsplitGP` branch — R2 verdict (B), §1.41), **both residuals are dischargeable and
the Leaf-3 producer is genuinely buildable.** Neither is a real gap:
- R1-affine dissolves (no de-homogenization; restate N1/N2 to bare LI `pbar`, feed the green homogeneous
  core directly). The *only* triple-LI input the homogeneous core needs (`LinearIndependent ![n_a,n_b,n_c]`)
  is the producer's own N3a-shaped construction — **not** GP (GP gives only pairwise), so it is supplied
  by the producer building its three real panel normals nonparallel, exactly as KT's eq.-(6.45) point
  choice does. (The pairwise `hgab` GP supplies is the *separate* placement-seed transversal of R2.)
- R3 is the bounded triangle mirror, no new notion.

So the program clears: the analytic `d=3` realization closes from green inputs + three bounded
to-build leaves (R1-consumer-restate, R3-simplicity, R2-signature-restate) + the producer assembly.

**Concrete remaining-commit estimate for Leaf 3 → phase close.** ~6–9 buildable commits:
1. **R1-consumer-restate** (RigidityMatrix.lean / Extensor.lean) — add `omitTwoExtensor_linearIndependent_of_li`
   (the affine-free Lemma 2.1, body verified to close); restate `span_omitTwoExtensor_eq_top` +
   `case_III_claim612` to bare `pbar : Fin 4 → ℝ⁴` + `LinearIndependent ℝ pbar` (the affine versions can
   stay as `homogenize`-specialized corollaries or be retired). Bounded, graph-free. (~1–2 commits.)
2. **R3 splitOff-simplicity** (Operations.lean) — `splitOff_simple_of_simple_of_noRigid` (or the
   `hloop`/`hpar`-style statement mirroring `rigidContract_simple`): the triangle-contradiction from
   `G.Simple` + `hnoRigid` + the degree-2/`e₀∉E` data, plus the triangle-is-0-dof brick. Graph-side,
   bounded. (~1–2 commits; the triangle-is-proper-rigid sub-brick may split off.)
3. **R2 producer-signature restate + Leaf 3 `hcand` discharge** (CaseI.lean; **§38 trap** at the seed) —
   restate `case_III_hsplit_producer` to the `hsplitGP` shape (`G.Simple` + conditioned IH, GP
   conclusion; pull `q` + `hgab` from the GP conjunct after discharging `(G.splitOff …).Simple` via R3),
   feed the homogeneous core for `pbar`/`hpbar` (R1), then discharge `hcand` with the L2b-place + per-line
   criterion already green (Leaf 2b done): build the candidate at the witness line, run
   `case_III_full_family_of_line` at `e_a`, feed C2. The §38-trap `hcand` discharge is the producer
   assembly. (~2–3 commits.)
4. **Leaf 4** — `theorem_55_generic (n:=2)(k:=2)` instance node, project `.2` (R2 ripple §1.41; the
   existing two-motive skeleton :1191–1206 absorbs it). Mint the small green blueprint node. (~1 commit.)
5. **Leaf 5** — `lem:case-II-realization`/`lem:case-III` blueprint flips + Thm 5.5→5.6 push feeding
   `rigidityMatrix_prop11`'s `hgen` (its `hub` lower bound already green). Unblocks Cor 5.7 at `d=3`.
   (~1 commit.)

The hard math is all behind us (the existential Claim 6.12, the line-indexed candidate placement, the
homogeneous core, the join↔meet bridge are green); the remaining work is bounded restatements + the two
bounded graph/algebra leaves + the §38-trap producer assembly. No research-shaped node remains on the
`d=3` route.

---

### 1.43 The R3-triangle-brick recon — verdict: a direct full-rank/tightness computation, NOT a circuit (at `d=3` the triangle is *exactly* `(D,D)`-tight, so no circuit exists); buildable, with the `n`-uniform route an explicit `D`-spanning-tree packing on `(K₃)̃` (2026-06-09)

> **Build-free design pass settling the one remaining R3 sub-leaf** — the triangle-0-dof brick
> `htri` that `splitOff_simple_of_noRigid` (Operations.lean:738) carries as a hypothesis: an `ab`-edge
> `f` (`G.IsLink f a b`) plus the `va`-edge `eₐ` and `vb`-edge `e_b` must yield `∃ H, H.IsProperRigidSubgraph
> G n`. §1.42's R3 verdict (A) closed the *bounded combinatorial* half and named this sub-brick
> "the project's `IsProperRigidSubgraph` + 0-dof machinery can state directly" but did not pin the
> *proof route*. This pass pins it. Read against the green Lean (`circuit_induces_isRigidSubgraph`
> Operations.lean:239, `rank_add_deficiency_eq` Deficiency.lean:994, `rank_matroidMG_le`
> Deficiency.lean:580, `matroidMG_indep_iff` Deficiency.lean:157, `IsProperRigidSubgraph`
> Deficiency.lean:381, `inducedSpan`/`fiberSpan` Operations.lean:44/51, `mulTilde_preconnected_of_isKDof_zero`
> Deficiency.lean:533 as the closest-pattern deficiency computation) + KT Lemma 6.7(ii) (p. 677). No
> `.lean`/`.tex` edits this pass.

**The witness subgraph.** The proper rigid subgraph is the **vertex-induced triangle** `H = G.induce {v,a,b}`
(equivalently the project's `inducedSpan` on the triangle's fibers — but `induce {v,a,b}` is the cleaner
witness, no fiber detour). Its three obligations:
- `H ≤ G` — `G.induce_le` on `{v,a,b} ⊆ V(G)` (`_hv`/`_ha`/`_hb` supply the inclusion).
- `V(H).Nonempty` — `{v,a,b}` is nonempty.
- `V(H) ⊂ V(G)` — **proper** because the splitting branch has `|V(G)| ≥ 4` (a 3-vertex graph is the
  base case `theorem_55_generic` handles directly, not via splitting; the degree-2 vertex `v` plus
  its two neighbours `a,b` are three of `≥ 4` vertices). This proper-ness needs a `|V(G)| ≥ 4` (or
  "`∃ w ∉ {v,a,b}`") hypothesis the brick must take — **not** currently on `splitOff_simple_of_noRigid`,
  so the brick's statement adds it (or threads it from the producer's `theorem_55_generic` branch
  guard). Flagged below.
- `H.IsKDof n 0` — `def(H̃) = 0`. **This is the genuine content**, settled next.

**The crux finding: `def((K₃)̃) = 0` is a full-rank computation, and at `d=3` the triangle is EXACTLY
`(D,D)`-tight — so there is NO circuit and the `circuit_induces_isRigidSubgraph` route does not apply.**
The triangle `H` on 3 vertices with edges `{va, vb, ab}` has `H̃ = (D-1)·H` carrying `3(D-1)` fiber
edges; full rank (hence `def = 0` via `rank_add_deficiency_eq`: `rank + def = D(|V|-1) = 2D`) needs
`rank M(H̃) = 2D`. The edge budget vs the rank target:
- `3(D-1) ≥ 2D ⟺ D ≥ 3 ⟺ bodyBarDim n ≥ 3 ⟺ n ≥ 2` (the regime KT works in). So the triangle has
  *enough* edges to be rigid exactly when `n ≥ 2`.
- **At `d=3` (`n=2`, `D=3`): `3(D-1) = 6 = 2D` — exactly tight.** The 6 multiplied edges are a *base*
  of `M(H̃)`; `H̃` is `(D,D)`-tight, packing `D=3` edge-disjoint spanning trees on 3 vertices (each tree
  = 2 edges, `3·2 = 6`). **No circuit lives inside the `d=3` triangle**, so the existing rigid-subgraph
  constructor `circuit_induces_isRigidSubgraph` (which needs a *dependent* circuit) cannot produce it.
- For `n ≥ 3` (`D ≥ 6`): `3(D-1) > 2D` strictly — the triangle is over-tight, a circuit exists, and the
  circuit route *would* apply. But the brick is consumed by the producer at parametric `n` (Leaf 3
  instantiates `theorem_55_generic` at `n` then specializes to `n=2` only at Leaf 4), so the brick must
  hold **uniformly in `n ≥ 2`** — meaning the exactly-tight `n=2` case must be covered, so a circuit
  route is insufficient regardless.

**The `n`-uniform buildable route.** Prove `rank M(H̃) = 2D = D(|V(H)|-1)` directly, both bounds:
- *Upper:* `rank_matroidMG_le H n hVne` gives `rank ≤ D(|V(H)|-1) = 2D` (green, no triangle specifics).
- *Lower:* exhibit an independent set of size `2D` in `M(H̃)`. By `matroidMG_indep_iff` (boundary-regime
  cleanliness), independence = `(D,D)`-sparsity of the restriction. The natural witness is the
  **`D`-spanning-tree packing of `(K₃)̃`**: partition the `3(D-1)` fibers into `D` forests each acyclic
  on `{v,a,b}`, take `2D` of them spanning. Concretely, the cleanest Lean: a `(D,D)`-tight fiber set of
  size `2D` on the 3-vertex triangle. The arithmetic (`(D,D)`-sparsity of an explicit `2D`-fiber
  selection on 3 vertices) is bounded; the spanning-tree packing existence is the body-hinge-Tay /
  Tutte–Nash-Williams content already in tree for the boundary regime (Phase 13/15) — `H̃` `(D,D)`-tight
  ⟺ packs `D` spanning trees is exactly `Graph.tutte_nash_williams` / `isSpanningTreePacking_of_isTight`.
  So the lower bound reduces to "the triangle `(K₃)` is `(D,D)`-tight", a finite sparsity count.
- Then `def(H̃) = 0` is `omega` off `rank_add_deficiency_eq` with both bounds (the `mulTilde_preconnected_of_isKDof_zero`
  / `two_le_crossingEdges_of_isKDof_zero` pattern at Deficiency.lean:469–576 is the model for assembling
  these `partitionDef`/`rank` facts).

**Scope verdict — buildable, but a genuine count, NOT a one-liner; this is its own commit (or two).**
The brick is a real `(D,D)`-tightness computation on an explicit 3-vertex multigraph, routed through the
already-green Tutte–Nash-Williams tree-packing + the rank bridge — no new research-shaped content, but
not a trivial mirror either. The cleanest factoring:
1. **A triangle-tightness lemma** `Graph.<triangle>.IsTight (bodyBarDim n) (bodyBarDim n)` (or directly
   `def = 0`): the 3-vertex / 3-edge graph is `(D,D)`-tight for `D ≥ 3`. Likely a small fresh lemma
   stating `(K₃)̃` packs `D` spanning trees, or the sparsity count directly. (~1 commit.)
2. **The `htri` discharge** in Operations.lean: assemble the `IsProperRigidSubgraph` witness `G.induce
   {v,a,b}` from the tightness lemma + `induce_le` + the proper-ness `|V(G)| ≥ 4` guard. (~part of the
   same or a follow-on commit.)

**Statement adjustment flagged for the brick.** `splitOff_simple_of_noRigid`'s `htri` is consumed with
`f` such that `G.IsLink f a b`; the brick's hypotheses are then `_hG_ea : G.IsLink eₐ v a`, `_hG_eb :
G.IsLink e_b v b`, the `ab`-edge `f`, and a **proper-ness guard** (`∃ w ∈ V(G), w ∉ {v,a,b}` or `4 ≤
V(G).ncard`). The producer supplies this from the splitting branch's standing `|V(G)| ≥ 4` (KT §6.4 only
splits when the base case `|V|=2`/small-graph is not reached). Thread it through `case_III_hsplit_producer`
as a hypothesis (it is true on the live `theorem_55_generic.hsplit` branch) — verify the exact form when
wiring Leaf 3.

**Why this is the prerequisite for both R3 and Leaf 3.** `splitOff_simple_of_noRigid` carries `htri`
green-modulo; discharging it (a) completes R3 (`(G.splitOff …).Simple` becomes hypothesis-free given
`G.Simple` + `hnoRigid` + the split data + the proper-ness guard), and (b) is consumed inside Leaf 3's
producer-signature restate (the `hsplitGP` shape needs `(G.splitOff …).Simple` to pull the GP `hgab`).
So this brick lands first, then Leaf 3's restate can call the now-complete `splitOff_simple_of_noRigid`.

---

### 1.44 The three Leaf-3 producer sub-obligations adjudicated against the Lean — GAP 1 verdict (C) (genuine hole: `|V(G)|=3` IS reachable in the project's `hsplit` branch, so the `4 ≤ |V|` proper-ness guard is unmet and the triangle witness is improper), GAP 2 verdict (C) (genuine hole: the candidate's eq.-(6.12) sheared seed is degenerate by construction, so the producer cannot conclude the GP motive's `IsGeneralPosition`/`AlgebraicIndependent ℚ` conjuncts the way `case_I_realization` does), GAP 3 verdict (A) (bounded: the bad-`t` set is a single value, a good `t` exists) (2026-06-09)

> **Build-free design pass settling the three sub-obligations the Leaf-3 concrete-seed producer
> (`case_III_hsplit_producer` restated to `theorem_55_generic.hsplitGP`) carries, BEFORE the §38-trapped
> producer build consumes them.** This pass is the latest instance of the recurring pattern (R1 →
> R1-affine genericity, R3 → triangle-is-not-a-circuit): every time the build neared the bounded core a
> new obligation the high-level recons (§1.40/§1.41/§1.42, "no research-shaped node remains") had not
> captured surfaced. Two of the three are now found to be **genuine holes**, not bounded residuals. The
> §1.41/§1.42 verdicts examined the GP-motive *inputs* (consume the GP `_hsplit`) and the simplicity
> *brick* in isolation; neither examined GAP 1's *reachability* against the actual reduction skeleton nor
> GAP 2's GP-motive *output* against the actual candidate seed. Verified against the green Lean
> (`minimal_kdof_reduction` ForestSurgery.lean:992 — the reduction's branch logic; `case_III_hsplit_producer`
> CaseI.lean:3970; `case_III_realization_of_line` :3901 — concludes the **bare** `HasFullRankRealization`;
> `hasFullRankRealization_of_independent_rigidityRow` :2167; `hasFullRankRealization_of_candidateSelector`
> :2204; `case_I_realization` :1999 + `hasGenericFullRankRealization_of_couple_blockTriangular_ofNormals_set`
> :1808 — how the GP conjuncts are built for the CONTRACT case; `HasGenericFullRankRealization`
> PanelHinge.lean:1033; `IsGeneralPosition` :121; `theorem_55_generic` :1154/`hsplitGP` :1167;
> `splitOff_simple_of_noRigid_of_card` Operations.lean:833 + `triangle_isProperRigidSubgraph` :783;
> `case_III_old_new_blocks_of_line` CaseI.lean:3529 + `hnewtrans` :3548; `panelSupportExtensor_add_smul_left`
> PanelLayer.lean:251) and **KT Lemma 6.7 / Lemma 6.8 read in full from the 2011 DCG PDF** (p. 677). No
> `.lean`/`.tex` edits this pass.

**GAP 1 — the `4 ≤ |V(G)|` proper-ness guard. Verdict (C): genuine hole — `|V(G)|=3` IS reachable in
the project's `hsplit` branch, and there the triangle witness is improper.** This is the most consequential
finding of the pass; it refutes the standing §1.42/§1.43 assumption ("the splitting branch never reaches
the `|V|≤3` base case").

- *KT carves out `|V|=3` as a separate base; the project does NOT.* KT Lemma 6.7(i) (p. 677) is explicit:
  *"If `|V|=3`, then `k=0` and there is a nonparallel realization satisfying `rank = D(|V|−1)`"* — at
  `|V|=3` a 2-edge-connected simple no-proper-rigid graph is a **triangle**, realized **directly by
  Lemma 5.4**, *not* by splitting off. Lemma 6.7(ii) (the `G_v^{ab}` simplicity argument the project's
  R3 mirrors) is stated *"If `|V|≥4`"*. So KT's manual case split never splits a `|V|=3` graph.
- *The project's reduction has no `|V|=3` base — it splits the triangle.* `minimal_kdof_reduction`
  (ForestSurgery.lean:1011–1047) inducts on `|V(G)|` with **only a `|V|=2` base** (`hbase`, :1015). For
  `|V|≥3` (:1017, `hV3 : 3 ≤ |V(G)|`) it does `by_cases hrig` on the existence of a proper rigid subgraph:
  proper-rigid → `hcontract`; **no proper-rigid → `hsplit`** (:1021, `exists_degree_eq_two` →
  `exists_splitOff_data_of_degree_eq_two` → `splitOff` to `|V|−1`). A `|V|=3` triangle is a minimal
  `0`-dof-graph (KT Lemma 6.7(i)) with **no proper rigid subgraph** (every proper subgraph has `≤2`
  vertices, so cannot be a rigid subgraph in the molecular regime `D≥3`), so it falls into the `hsplit`
  branch with `|V(G)|=3` exactly. `splitOff` then lands on `|V|=2` (the IH base). **So the `hsplit`
  producer IS invoked at `|V(G)|=3`.**
- *There the triangle witness is genuinely improper.* `triangle_isProperRigidSubgraph` (Operations.lean:783)
  builds `H = G.induce {v,a,b}` and proves it *proper* only via `4 ≤ V(G).ncard` (:820–825: if
  `{v,a,b} = V(G)` the witness is the whole graph, *not* a proper subgraph). At `|V(G)|=3`, `{v,a,b}` IS
  all of `V(G)`, so the triangle is improper — `triangle_isProperRigidSubgraph` is *false* there, and
  `splitOff_simple_of_noRigid_of_card`'s `4 ≤ |V|` hypothesis is genuinely unmet, not merely missing a
  thread. The R3 simplicity discharge as built **does not apply at `|V(G)|=3`.**
- *Simplicity itself still holds at `|V|=3`, but the R3 lemma is the wrong tool.* When `G` is the
  triangle, `splitOff v a b e₀` is the 2-vertex single-edge graph on `{a,b}` (`vertexSet_splitOff`,
  `edgeSet_splitOff`), which is trivially simple (one edge, no loop, no parallel pair). So the *fact*
  `(G.splitOff …).Simple` is true at `|V|=3` — but it must be obtained by a **second, small route** (the
  `|V|=2`-output direct simplicity), not by the triangle-contradiction. R3 covers only `|V|≥4`.
- *The unblock.* Two clean options, both bounded: **(i)** add a hypothesis-free `|V(G)|=3` (`G.splitOff`
  has `|V|=2`, simple by direct edge-count) branch to the simplicity discharge — a small case-split lemma
  `splitOff_simple_of_…` that is `splitOff_simple_of_noRigid_of_card` for `|V|≥4` and the direct 2-vertex
  argument for `|V|=3` — OR **(ii)** confirm the producer can take `3 ≤ |V(G)|` and split: the genuine
  question is whether the *whole Leaf-3 candidate completion* is sound at `|V|=3`, not just simplicity
  (the eq.-(6.12) old-block `case_III_old_new_blocks_of_line` needs `V(Gv) = V(G)∖{v}` nonempty — true at
  `|V|=3`, `|V(Gv)|=2`, and the OLD block has `D(2−1)=D` rows; the count arithmetic must be re-checked at
  `|V(G)|−1=2`). **Recommended:** (i) — supply `(G.splitOff …).Simple` at `|V|=3` directly, keep R3 for
  `|V|≥4`, and let the rest of the candidate completion run uniformly (its count is parameterized over
  `|V(G)|`, so `|V|=3` is not special for the row algebra, only for the simplicity brick). This is a new
  bounded leaf, **but it is a hole the current build would hit** — the producer cannot discharge
  `(G.splitOff …).Simple` for a general `G` on the `hsplit` branch with only `splitOff_simple_of_noRigid_of_card`.

**GAP 2 — the GP-conclusion conjuncts. Verdict (C): genuine hole — the eq.-(6.12) candidate seed is
degenerate by construction, so the `IsGeneralPosition` and (especially) `AlgebraicIndependent ℚ`
conjuncts of `HasGenericFullRankRealization` cannot be produced the way `case_I_realization` produces
them.** The R2 verdict (§1.41) correctly established that the producer must *consume* the GP `_hsplit` to
get `hgab`; it did **not** examine that the producer must also *conclude* `HasGenericFullRankRealization`,
whose four conjuncts the candidate-completion route does not deliver.

- *What `case_I_realization` does, read end-to-end — and why it is NOT reusable for the split candidate.*
  `case_I_realization` (:1999) concludes `HasGenericFullRankRealization` by routing through
  `hasGenericFullRankRealization_of_couple_blockTriangular_ofNormals_set` (:1808), which builds the GP and
  alg-indep conjuncts at a **generic, algebraically-independent** seed `q₀ := exists_injective_algebraicIndependent_real`
  (:1857) — the seed is a simultaneous non-root of the `H`-leg rank polynomial `Q_H`, the contraction rank
  polynomial `Q_c`, AND the general-position polynomial `Q_gp` (`exists_generalPosition_polynomial`,
  PanelHinge.lean:375, :1846), so `hgp := hQgp_pos q₀ hq₀gp` (:1864) gives `IsGeneralPosition` and `halg`
  gives the alg-indep conjunct, both for free at that generic seed. The block-triangular coupling reads
  rigidity off **two generic legs** — it never builds a degenerate placement. **The Case-III candidate
  completion is structurally the opposite:** `case_III_realization_of_line` (:3901) routes through
  `hasFullRankRealization_of_candidateSelector` (:2204) → `hasFullRankRealization_of_independent_rigidityRow`
  (:2167), which builds at the **fixed eq.-(6.12) sheared seed `q₀`** where `v`'s normal is `n_a + t•n'`
  (CaseI.lean:3544, `hq₀`) and concludes only the **bare** `HasFullRankRealization` (:3918). The whole
  point of the seed is to put the `va`-hinge collinear with the witness line `L` — i.e. to place `v`'s
  panel in a *special* (degenerate) position relative to `a`'s. There is **no generic-seed freedom** in
  the candidate route: the seed is determined by the witness line.
- *`IsGeneralPosition` (pairwise) reduces to GAP 3 + the IH GP, so this conjunct alone is borderline-bounded.*
  `IsGeneralPosition (ofNormals G ends q₀)` (PanelHinge.lean:121) is `∀ a' b', a'≠b' → LinearIndependent
  ![normal a', normal b']`. At the candidate seed the normals are: `v ↦ n_a + t•n'`, all others `= q`'s.
  The pairs not involving `v` are GP iff the IH split-off seed `q` is GP (from the GP `_hsplit`). The
  `v`-`a` pair `![n_a + t•n', n_a]` is independent iff `n'∦n_a` and `t≠0` (= `hane`, supplied by `hL`).
  The `v`-`b` pair `![n_a + t•n', n_b]` is **exactly GAP 3's `hnewtrans`** (so it reduces to the producer's
  free `t`). The `v`-`u` pairs for other `u` need `t` generic against finitely many lines. So
  `IsGeneralPosition` of the candidate seed *is* obtainable by choosing `t` generically — bounded,
  overlapping GAP 3. **This half is (B).**
- *`AlgebraicIndependent ℚ` is the genuine hole.* The fifth conjunct of `HasGenericFullRankRealization`
  (PanelHinge.lean:1038) is `AlgebraicIndependent ℚ (fun (a',i) ↦ Q.normal a' i)` — the flattened seed
  alg-independent over `ℚ`. This is KT's footnote-6 standing inductive choice (p. 685), consumed by the
  Claim-6.11 kernel. But the candidate seed has `v`'s normal `= n_a + t•n'` — an **explicit `ℚ`-algebraic
  (indeed `ℝ`-linear) combination** of `a`'s normal and the witness normal. So the flattened candidate
  seed is **algebraically dependent over `ℚ` by construction**: it can NEVER be `AlgebraicIndependent ℚ`.
  No choice of `t` repairs this — the dependence is in the *shape* of the seed, not its parameter. The
  candidate-completion route fundamentally cannot deliver the alg-indep conjunct. (Contrast Case I: its
  generic seed `exists_injective_algebraicIndependent_real` is alg-indep *because* it is unconstrained.)
- *Why this is (C), not (B).* (B) would be "the conjuncts are buildable but need a named new piece." The
  alg-indep conjunct is **not buildable at the candidate seed at all** — the seed is dependent by
  construction. The producer concludes `HasGenericFullRankRealization` only if it can exhibit *some* `Q`
  carrying all five conjuncts; the candidate-completion `Q = ofNormals G ends q₀` carries the bare
  rigidity but provably not the alg-indep. **Resolution candidates (each itself unverified — this is the
  research-shaped residual):** (a) the conjunct is consumed only as a *non-root certificate* for rank
  polynomials (`MvPolynomial.eval_ne_zero_of_coeffs_subset_range_of_algebraicIndependent`), so perhaps the
  Case-III producer can supply a *weaker* certificate (the degenerate seed is a non-root of the specific
  Case-III rank polynomial directly, without alg-independence) — but the *motive* asks for alg-independence,
  not a per-polynomial non-root, so this needs a **motive weakening / re-shaping** of
  `HasGenericFullRankRealization`'s fifth conjunct, a cross-cutting change touching every producer; (b)
  re-realize: after fixing the candidate placement to get bare rigidity, perturb to a nearby *generic*
  seed that is still rigid (rigidity is Zariski-open) AND alg-indep — but then the GP-motive's link to the
  *specific* witness line `L` is lost, and it is unclear the perturbed seed still certifies the same
  Claim-6.12 selection. **Neither is the clean mirror §1.41 assumed.** This is a genuine architectural
  question the build would hit at the producer-signature restate, NOT a bounded thread.
- *KT cross-check — does KT claim GP output for the split case?* Yes: Lemma 6.8 (p. 677) concludes *"a
  nonparallel realization"*, and eq. (6.12) chooses `Π°` *"not parallel to `Π(u)` for `u ∈ V∖{v}`"* — so
  KT's realization is nonparallel (= `IsGeneralPosition`). But KT works over a transcendence basis
  implicitly (footnote 6's alg-indep choice is a *global* convention, not re-derived per construction);
  the Lean motive makes the alg-indep conjunct **explicit**, and the eq.-(6.12) shear breaks it. KT's
  prose nonparallel-realization claim is faithful to the `IsGeneralPosition` half (the (B) half above);
  the `AlgebraicIndependent ℚ` half is a Lean-formalization artifact of how footnote 6 was internalized
  (Phase 22d, PanelHinge.lean:1017–1031) — it is the conjunct the candidate seed cannot honor.

**GAP 3 — the `hnewtrans` genericity-in-`t`. Verdict (A): bounded — the bad-`t` set is at most a single
value, so a good `t` exists; route named.** `case_III_old_new_blocks_of_line` (CaseI.lean:3548) carries
`hnewtrans : LinearIndependent ![n_a + t•n', n_b]` as an explicit hypothesis the producer (choosing `t`)
must supply. (The fixed-`n_b` case got it free from `hgab` via `panelSupportExtensor_add_smul_right`'s row
reproduction, PanelLayer.lean:238 — but that identity holds **only at `n' = n_b`**, hence the explicit
hypothesis for an arbitrary witness `n'`.)

- *The bad set is a single value.* `![n_a + t•n', n_b]` fails to be independent iff `n_a + t•n' ∈ span{n_b}`
  or `n_a + t•n' = 0`. The affine line `t ↦ n_a + t•n'` (direction `n'`, base `n_a`) is contained in the
  line `span{n_b}` iff both `n_a ∈ span{n_b}` *and* `n' ∈ span{n_b}`; but `hgab : LinearIndependent
  ![n_a, n_b]` (the pairwise GP from the GP `_hsplit`) gives `n_a ∉ span{n_b}`, so the affine line is NOT
  contained in `span{n_b}` — hence meets it in **at most one** `t`. The vanishing `n_a + t•n' = 0` is also
  at most one `t` (`n' ≠ 0` from `hL`). So the bad set `{t : ¬LinearIndependent ![n_a+t•n', n_b]}` has
  cardinality `≤ 2` (in fact a single value plus possibly the vanishing point); `ℝ` is infinite, so a good
  `t ≠ 0` exists.
- *The route.* This is the classic "an affine line not contained in a 1-dim subspace meets it in ≤1 point."
  In Lean: `LinearIndependent ![u, w] ↔ ¬∃ s, u = s•w` (for `w≠0`) via `linearIndependent_fin2` /
  `LinearIndependent.pair_iff`; the equation `n_a + t•n' = s•n_b` is, projecting against a functional
  separating `span{n_b}` from `n_a`, a single linear constraint on `t` with nonzero coefficient (the
  coefficient is the same functional applied to `n'`; if it is zero then `n' ∈ span{n_b}^⊥`-direction and
  the line never meets `span{n_b}`, so the bad set is empty). Either way the bad `t`-set is finite. The
  cleanest Lean is likely a small lemma `∃ t, t ≠ 0 ∧ LinearIndependent ![n_a + t•n', n_b]` from
  `hgab`/`hL` + `Set.Finite`/infinite-`ℝ`. **Bounded, ~part of the producer assembly; no new geometry**
  (it is `Fin (k+2) → ℝ` linear algebra, graph-free, off the §38 trap).
- *Overlap with GAP 2.* `hnewtrans` is *exactly* the `v`-`b` pair of `IsGeneralPosition` (GAP 2's (B)
  half). So the same good-`t` choice discharges GAP 3 AND the pairwise-GP half of GAP 2 at once. It does
  **not** touch GAP 2's alg-indep hole (that is shape-level, not `t`-level).

**COMBINED VERDICT — the Leaf-3 concrete-seed producer is NOT genuinely buildable as scoped; two of the
three sub-obligations are genuine holes.** GAP 3 is bounded (A). GAP 1 (C) and GAP 2 (C) are real:
- **GAP 1** — the `4 ≤ |V(G)|` guard is genuinely unmet at the reachable `|V(G)|=3` triangle, where the
  R3 triangle witness is improper. **Unblock (bounded):** a small `|V(G)|=3` simplicity branch
  (`splitOff` lands on `|V|=2`, simple by direct edge-count), keeping R3 for `|V|≥4`. This is a missed
  case, not a research obstacle — but it IS a hole the current build hits.
- **GAP 2** — the producer must conclude `HasGenericFullRankRealization` (R2's `hsplitGP` shape), but the
  eq.-(6.12) candidate seed is degenerate by construction and **cannot carry the `AlgebraicIndependent ℚ`
  conjunct** (the `IsGeneralPosition` conjunct reduces to GAP 3, bounded). This is the research-shaped
  residual: it needs either a **motive re-shaping** (weaken the fifth conjunct to a per-polynomial non-root
  certificate the degenerate seed can supply) or a **re-realization** (perturb to a generic alg-indep
  rigid seed while preserving the Claim-6.12 selection) — neither verified, both cross-cutting. **This is
  the genuine architectural question the §38-trap producer build would hit; it should be settled (math-first)
  before the producer is restated to `hsplitGP`.**

**Why the high-level recons missed these (the lesson, for the friction log).** §1.41/§1.42 verified the
GP-motive *inputs* and the simplicity *brick* in isolation, against the *statements* of the green lemmas,
without tracing (a) GAP 1: the producer's `4 ≤ |V|` guard back through `minimal_kdof_reduction`'s branch
logic to confirm reachability, and (b) GAP 2: the producer's *conclusion* (`HasGenericFullRankRealization`,
five conjuncts) against the *fixed-degenerate-seed* route `case_III_realization_of_line` actually concludes
(bare `HasFullRankRealization`). The pattern (§1.39 effort-accounting, R1, R3) holds again: **recon the
target node's proof route end-to-end against the consuming skeleton, not just its statement** — the
design-pass-first discipline's red-node consistency gate (top-level `CLAUDE.md`) is exactly this, and it
caught GAP 1/GAP 2 here only because this pass re-read the *route*, not the verdicts.

### 1.45 GAP 2 resolution — VERDICT (B-derive): the bare→generic single-graph upgrade IS derivable from the green rank-polynomial machinery, is L-independent, and is faithful to how KT actually concludes Lemma 6.8 (KT builds the degenerate witness and invokes Lemma 5.2's "convert to nonparallel without decreasing rank"); GAP 2 dissolves into "build the degenerate candidate (bare full rank) + invoke the upgrade" (2026-06-09)

> **Build-free design pass settling GAP 2 (§1.44), the research-shaped producer blocker.** The question:
> does the producer have to *conclude* `HasGenericFullRankRealization` at the eq.-(6.12) degenerate seed
> (which it provably cannot — the seed is `ℚ`-algebraically dependent by construction), or can it conclude
> the GENERIC realization is full-rank via a single-graph "full rank is Zariski-open" upgrade WITHOUT the
> candidate itself being generic? **Verdict: the upgrade route is correct, the green machinery already has
> every brick, and it is exactly KT's own argument.** Verified against the green Lean
> (`HasGenericFullRankRealization` PanelHinge.lean:1033 — the realization is **existentially quantified**;
> `exists_rankPolynomial_of_rigidOn` GenericityDevice.lean:1159 — the bare→rank-polynomial brick;
> `exists_injective_algebraicIndependent_real` + `eval_ne_zero_of_coeffs_subset_range_of_algebraicIndependent`
> Mathlib/RingTheory/MvPolynomial/Tower.lean:69; `hasGenericFullRankRealization_of_splice_ofNormals`
> GenericityDevice.lean:914 — the "rigid GP alg-indep seed → generic motive" assembly pattern;
> `case_I_realization` CaseI.lean:1857/1864/1934 — how the GP conjuncts are built; `exists_good_realization`
> GenericityDevice.lean:109 + its header :43–46 "rank is lower semicontinuous, attains its maximum on a
> Zariski-open generic set"; `case_III_old_new_blocks_of_line` CaseI.lean:3529–3548 — the seed shears ONLY
> body `v`) **and KT 2011 read in full** (p. 662 footnote 4 / generic = alg-indep maximizes rank; Lemma 5.2
> p. 671; Lemma 6.8 + Claim 6.9 + eq. (6.12) pp. 677–678, the "ΠG,p1(v) and ΠG,p1(a) are parallel … convert
> to nonparallel by Lemma 5.2 without decreasing rank" passage). No `.lean`/`.tex` edits this pass.

**The genericity-device read — `HasGenericFullRankRealization` is L-free and seed-free in its statement.**
The motive (PanelHinge.lean:1033) is `∃ Q, Q.graph = G ∧ Q.IsGeneralPosition ∧ …rigid… ∧ links ∧
AlgebraicIndependent ℚ (normals)`. **The realizing `Q` is existentially bound** — the motive asks only that
*some* framework on `G` carry all five conjuncts; it does NOT fix a seed, and it never mentions `L`. So the
producer's job is not "make the candidate seed generic" (impossible) but "exhibit *some* generic alg-indep
rigid framework on `G`". The witness line `L` is scaffolding to exhibit *one* full-rank realization; once
full rank is witnessed anywhere, genericity supplies a different `Q`. This is the whole point of Claim 6.12
(§1.39): produce one full-rank witness, let genericity do the rest.

**The bare→generic upgrade exists as green machinery (no packaged single-graph lemma yet — bounded new
leaf).** The route, all bricks green:
1. `case_III_realization_of_line` (CaseI.lean:3901) already produces the **bare** `HasFullRankRealization k
   G`, witnessed by the degenerate `ofNormals G ends q₀` (C1, `hasFullRankRealization_of_independent_rigidityRow`).
2. From that bare witness, `exists_rigidOn_ofNormals_of_hasFullRankRealization` (GenericityDevice.lean:1125)
   recovers `(ends, q₀)` with `ofNormals G ends q₀` rigid on `V(G)`.
3. `exists_rankPolynomial_of_rigidOn` (GenericityDevice.lean:1159) turns that single rigid seed into a
   **rational** `MvPolynomial Q ≠ 0` (`eval q₀ Q ≠ 0`, `Q.coeffs ⊆ range (algebraMap ℚ ℝ)`) whose every
   non-root `q` carries `≥ D(|V|−1)` independent panel rows of `ofNormals G ends q`. **`Q` is built from
   `g q i := (ofNormals G ends q).panelRow ends i` and `c i j` = body-incidence sign × `annihRowPoly`
   (:1198–1204) — functions of `G` and `ends` ONLY; the seed `q₀` enters solely through `eval q₀ Q ≠ 0`,
   and `L` enters nowhere.** This is the formal L-independence: the rank polynomial is a property of the
   graph, not the placement.
4. `exists_injective_algebraicIndependent_real (α × Fin (k+2))` gives an injective `ℚ`-alg-indep seed `q₁`;
   `eval_ne_zero_of_coeffs_subset_range_of_algebraicIndependent` (Tower.lean:69) certifies `eval q₁ Q ≠ 0`,
   so `ofNormals G ends q₁` is full-rank — AND `q₁` is alg-indep (the fifth conjunct) AND general position
   (an alg-indep seed is pairwise-independent; the `case_I_realization` route gets `IsGeneralPosition` for
   free at exactly this seed via `exists_generalPosition_polynomial`, threaded into the same triple product,
   CaseI.lean:1846/1864). The witness `Q = ofNormals G ends q₁` then satisfies all five conjuncts of
   `HasGenericFullRankRealization` — exactly the `hasGenericFullRankRealization_of_splice_ofNormals`
   assembly pattern (GenericityDevice.lean:930–933), but for a single graph rather than a splice.

   This is a **bounded new leaf** — a single-graph upgrade lemma
   `hasGenericFullRankRealization_of_hasFullRankRealization` (working title): `HasFullRankRealization k G →
   HasGenericFullRankRealization k G`, body = steps 2–4, reusing `case_I_realization`'s own block (:1843–1936)
   nearly verbatim with the rank-polynomial product replaced by the single graph's `Q`. The one wrinkle is
   `exists_rankPolynomial_of_rigidOn`'s **all-edges `hne` (every hinge transversal at `q₀`)**: at the
   degenerate seed only the linking edges are guaranteed transversal (the `va`/`vb` hinges via
   `hane`/`hnewtrans`). The fix is already in tree — the **leg-restricted** `exists_rankPolynomial_of_rigidOn_linking`
   (:1252) needs `hne` only on *linking* edges (`G.IsLink e (ends e).1 (ends e).2 → supportExtensor e ≠ 0`),
   which the candidate completion supplies, and delivers the same `Q`. So step 3 uses the `_linking` variant.
   No new geometry; pure assembly of existing green bricks. **Estimate: 1 commit** (the upgrade lemma) once
   the producer's bare-`HasFullRankRealization` output (Leaf 3 concrete seed) exists.

**L-independence determination — CONFIRMED clean, the upgrade does NOT lose the Claim-6.12 selection.** The
generic full-rank conclusion is genuinely `L`-independent (the §1.44 suspicion is correct): (i) the rank
polynomial `Q` depends only on `G`/`ends` (step 3); (ii) `L` is consumed entirely *before* the upgrade — it
is the scaffolding that makes the degenerate candidate full-rank (`r̂(C(L)) ≠ 0` feeds the row-space
criterion), and once `HasFullRankRealization k G` is in hand, `L` has done its job and is discarded; (iii)
the downstream capstone consumes only `HasGenericFullRankRealization k G` (no `L`-dependence in
`theorem_55_generic`'s `hsplitGP` conclusion, PanelHinge.lean:1175, nor in `rigidityMatrix_prop11`'s `hgen`).
The generic realization is a different framework `Q = ofNormals G ends q₁` at the alg-indep seed `q₁`, with
`v`'s panel in *general* position — KT's "rotated `Π(v)`". Nothing `L`-specific survives into the output, so
there is no link to lose. This **refutes** the §1.44 worry "it is unclear the perturbed seed still certifies
the same Claim-6.12 selection": the selection is not a property of the output realization, it is the device
(Claim 6.12) that *found* a full-rank witness; the output need only be *some* generic full-rank realization.

**KT cross-check — KT builds a degenerate witness and invokes genericity; this IS resolution route (b),
done KT's way (not a perturbation that loses the selection).** KT Lemma 6.8 (p. 677) builds `(G, p1)` via
eq. (6.12) — `p1(va) = L`, `p1(vb) = q(ab)` — proves `rankR(G,p1) ≥ D(|V|−1) − k`, and explicitly notes
*"Although ΠG,p1(v) and ΠG,p1(a) are parallel in (G,p1), at the end of the proof we will convert (G,p1) to a
nonparallel panel-hinge realization by slightly rotating ΠG,p1(v) without decreasing the rank of the
rigidity matrix"* — citing **Lemma 5.2** (p. 671: a realization with exactly one equal/parallel pair `(a,b)`
has a nonparallel realization of `rank ≥` it). KT's footnote-4 / p. 662 definition makes generic = alg-indep
and states *"the rank of R(G,p) takes the maximum value over all nonparallel realizations if (G,p) is
generic"*. So KT's own argument is: **degenerate witness → rank lower bound → genericity (max rank) gives the
nonparallel realization at ≥ that rank**. The Lean rank-polynomial route (steps 2–4) is the faithful
formalization: `exists_rankPolynomial_of_rigidOn` is the "rank is a polynomial, nonzero somewhere ⟹ nonzero
generically" content of footnote 4 + Lemma 5.2 combined; the alg-indep seed `q₁` is KT's "generic
nonparallel realization". The §1.44 resolution (a) (motive-weakening to a per-polynomial non-root) is NOT
needed and would diverge from KT; resolution (b) (re-realize generically) is the right one, and it is L-clean
because the upgrade reads off the graph's rank polynomial, not the degenerate placement.

**RECLASSIFIED — GAP 2 is bounded (B-derive), not research-shaped.** The §1.44 "(C) genuine hole,
research-shaped" verdict is **overturned**: there is no architectural question. The producer concludes
`HasGenericFullRankRealization k G` by (1) building the degenerate candidate to bare `HasFullRankRealization`
(Leaf 3 concrete seed, the §38-trap producer build, unchanged) then (2) the new bounded upgrade leaf. The
buildable-leaf path:
- **GAP-2 leaf (NEW, ~1 commit):** `hasGenericFullRankRealization_of_hasFullRankRealization` (GenericityDevice.lean
  or CaseI.lean) — steps 2–4 above, reusing the `case_I_realization` rank-polynomial block with the single
  graph's `_linking` rank polynomial. Graph-free over the abstract assembly except the `ofNormals` carrier
  the rank-polynomial brick already fixes (no *new* §38 surface — the bricks are green at that carrier).
- The producer (Leaf 3 concrete seed) builds bare `HasFullRankRealization`, then composes the GAP-2 leaf to
  conclude the generic motive `hsplitGP` wants — so the `hsplitGP` restate is unblocked. GAP 1 (the `|V|=3`
  branch) and GAP 3 (`hnewtrans` genericity-in-`t`) remain the two bounded sub-leaves §1.44 named; all three
  are now bounded. **Refreshed estimate to phase close:** GAP-2 upgrade leaf (~1) + GAP-1 `|V|=3` branch (~1)
  + GAP-3 good-`t` (folded into the producer assembly) + the §38-trap concrete-seed producer (~1–2) + Leaf 4
  `theorem_55_generic (n:=2)(k:=2)` instance (~1) + Leaf 5 flips/Thm 5.5→5.6 (~1) ≈ **5–6 commits**, back to
  a clean bounded close (no research-shaped node remains in Phase 22g; Lemma 6.10/Claim 6.11 the §4 risk
  register flags as the largest KT proof is already green via Phase 22d/22e/22f).

### 1.46 GAP 1 DISSOLVED — the producer never consumes `(G.splitOff …).Simple` (the GAP-2 B-derive route uses `hIH.2`'s bare conjunct); and §1.44's "supply `(G.splitOff …).Simple` directly at `|V|=3`" is FALSE (the `|V|=3` triangle's splitOff genuinely has a parallel pair) (2026-06-09)

> **Build-free recon pass re-tracing GAP 1 against the actual producer/IH wiring, after the GAP-2 leaf
> landed.** §1.44 flagged GAP 1 ((C), the "most consequential finding") as: the producer needs
> `(G.splitOff v a b e₀).Simple` (to feed the IH's *generic* conjunct), but `splitOff_simple_of_noRigid_of_card`
> needs `4 ≤ |V(G)|`, unmet at the reachable `|V(G)|=3` triangle; its proposed unblock (i) was a "small
> `|V(G)|=3` simplicity branch — `splitOff` lands on `|V|=2`, simple by direct edge-count." Re-reading the
> *route* (not the §1.44 verdict) against the now-green producer + `theorem_55_generic`'s `hsplitGP` shape,
> **GAP 1 is dissolved, and §1.44's unblock (i) is mathematically false.** Two findings:
>
> 1. **The producer never needs split-simplicity (GAP 1 dissolves under the §1.45 GAP-2 B-derive route).**
>    `theorem_55_generic`'s `hsplitGP` premise (PanelHinge.lean:1167–1175) hands the producer
>    `hIH : ((G.splitOff …).Simple → HasGenericFullRankRealization k (G.splitOff …)) ∧
>    HasFullRankRealization k (G.splitOff …)` together with `G.Simple`, and asks for
>    `HasGenericFullRankRealization k G`. Under §1.45 the producer (a) takes the **bare**
>    `_hsplit := hIH.2 : HasFullRankRealization k (G.splitOff …)` — the *unconditional* `.2` conjunct, no
>    `(G.splitOff …).Simple` required — feeds it to `case_III_hsplit_producer` to build the degenerate
>    candidate `ofNormals G ends q₀` to **bare** `HasFullRankRealization`, then (b) invokes
>    `hasGenericFullRankRealization_of_rigidOn_ofNormals` (CaseI.lean:1968, the landed GAP-2 leaf) to
>    re-realize it generically. Neither (a) nor (b) consumes `(G.splitOff …).Simple` (the upgrade reads
>    the graph's rank polynomial off the *fixed* concrete candidate, never the split graph). The IH's
>    *generic* `.1` conjunct — the only place `(G.splitOff …).Simple` would enter — is **unused**. So GAP 1
>    was an artifact of the pre-§1.45 plan (conclude GP *at the split graph* via the generic IH conjunct);
>    the B-derive route concludes GP *at `G`* from the bare candidate and discards the split-simplicity need.
>
> 2. **§1.44's unblock (i) is FALSE: `(G.splitOff …).Simple` does not hold at `|V(G)|=3`.** §1.44 line ~1632
>    asserted "when `G` is the triangle, `splitOff v a b e₀` is the 2-vertex single-edge graph on `{a,b}`,
>    trivially simple." This is wrong. At `|V(G)|=3`, `D=3`, a minimal `0`-dof `G` is `(D,D)`-tight so
>    `|E(G)| = D·(|V|−1)/(D−1) = 3·2/2 = 3` — i.e. `G` is the triangle, which DOES carry the `ab`-edge `f`
>    (`G.IsLink f a b`). In `splitOff v a b e₀` (Operations.lean:574), `f` survives via the first disjunct
>    (`f ≠ e₀` since `e₀ ∉ E(G)`, `G.IsLink f a b`, `a ≠ v`, `b ≠ v`) **and** the fresh `e₀` links `a-b` via
>    the second disjunct — two *distinct* edges `f ≠ e₀` on the pair `a-b` = a parallel pair, so
>    `(G.splitOff …)` is **not simple**. The split graph is the 2-vertex *double*-edge `K₂` (the same base
>    object `hbase`/`hbaseGP` handle, where GP genuinely fails — PanelHinge.lean:1125–1128), not a single
>    edge. So no `|V(G)|=3` simplicity branch exists to build; option (i) is unprovable.
>
> **Net:** GAP 1 needs no new lemma — it dissolves into the GAP-2 B-derive route already chosen. The
> originally-planned `|V|=3` simplicity branch is dropped (it was false). `R3` (`splitOff_simple_of_noRigid_of_card`,
> `|V|≥4`) stays exactly as a reusable graph-side fact (sibling of `rigidContract_simple`), even though the
> `d=3` producer no longer calls it — KT's Lemma 6.7(ii) `G_v^{ab}`-simplicity at `|V|≥4` is genuine math
> that re-enters anywhere a *simple* split realization is wanted (e.g. a future unconditional-GP variant or
> Phase 23). The remaining `d=3` work is unchanged minus GAP 1: the §38-trap concrete-seed producer (composing
> the landed GAP-2 upgrade onto the bare candidate, folding in GAP-3 good-`t`), then Leaf 4/5. **This is again
> the "recon-traces-the-route, not the verdicts" lesson §1.44 named** — §1.44 itself adjudicated GAP 1 as a
> *brick* ("the `4 ≤ |V|` guard is unmet") without tracing whether the producer/IH wiring (post-§1.45) ever
> reaches for the brick, and asserted a `|V|=3` simplicity fact without checking the triangle's edge count.

### 1.47 Coordinator cross-check — §1.46's GAP-1 dissolution is UNSOUND (it orphans `hgab`); the corrected picture is `|V|≥4` buildable (needs the GP `.1` conjunct + R3) / `|V|=3` a GENUINE HOLE (the triangle base case) (2026-06-09)

> **Coordinator verdict-reasoning check on the §1.46 recon commit (not a build/recon pass — a correction
> landed at the user's pause-and-evaluate checkpoint).** §1.46 was mechanically clean (docs-only, on master)
> but its headline finding — "GAP 1 dissolves: the producer takes the bare `hIH.2` and the GP `.1` conjunct
> is unused" — does **not** close. It is the coordinate-phase step-3 failure mode: a recon that *re-routes*
> to dissolve one gap without re-verifying the producer's **other** carried obligations still close under the
> new route. §1.46 finding-(2) (the `|V|=3` splitOff is a non-simple double-edge `K₂`) is **sound and stands**;
> finding-(1) ("dissolved, `.1` unused") is **retracted**.

**The orphaned `hgab` (the airtight chain).**
- The producer's candidate placement `case_III_old_new_blocks_of_line` (CaseI.lean:3454) takes
  `hgab : LinearIndependent ℝ ![q(a,·), q(b,·)]` as an **explicit hypothesis** (and `hnewtrans` at :3635).
- GAP-3's "bounded" verdict (§1.44, line ~1725) derives its good-`t` **from `hgab`**: *"`hgab` (the pairwise
  GP from the GP `_hsplit`) gives `n_a ∉ span{n_b}`"*. So `hnewtrans` needs `hgab`.
- R2 (§1.41) and GAP-3 both source `hgab` from the **GP `.1` conjunct's `IsGeneralPosition`** — and §1.44
  established a *bare* rigid realization does NOT force `ab`-transversality (the non-simple regime has
  parallel panels), so `hIH.2` cannot supply `hgab`.
- §1.46 declares the `.1` conjunct **unused**. ⟹ `hgab` is orphaned: the candidate placement requires it,
  its only established source is the `.1` §1.46 discards. §1.46 conflated *"the producer needn't conclude GP
  at the split graph for the final answer"* (true — it concludes GP at `G` via the GAP-2 upgrade) with *"the
  producer needn't use `.1` at all"* (false — it needs `.1`'s `IsGeneralPosition` for `hgab` to build the
  candidate).

**The corrected picture (to confirm against the Lean in the next session's recon, not asserted settled):**
- **`|V(G)| ≥ 4`: buildable, but `.1` and R3 are ON the route (not off it).** `splitOff` is simple (R3:
  a parallel pair would give the triangle as a *proper* rigid subgraph, contradicting `hnoRigid`), so the GP
  `.1` antecedent `(G.splitOff …).Simple` holds → `.1` yields a *generic* split realization → `hgab` (every
  pair transversal). The producer uses `.1` (for `hgab`) **and** the GAP-2 upgrade (for the generic-`G`
  conclusion). [Alt: route-B — upgrade the bare `.2` split realization to generic via the GAP-2 leaf — needs
  `hne` extracted from the bare existential, the same open requirement the GAP-2 leaf flagged; route-A via
  `.1` is cleaner here.]
- **`|V(G)| = 3`: a GENUINE HOLE — the triangle base case.** `splitOff` is the non-simple double-edge `K₂`
  (§1.46-(2), sound) → the GP `.1` antecedent is **false**, AND `K₂` is the base object where GP genuinely
  fails (PanelHinge.lean:1125–1128) so the bare→generic upgrade cannot manufacture GP for the split either →
  `hgab` is unavailable by **either** route → the producer cannot build the candidate at `|V|=3`. The project's
  `minimal_kdof_reduction` routes the `|V|=3` triangle into the `hsplit` branch (no proper rigid subgraph, only
  a `|V|=2` base), but the `hsplit` producer cannot discharge it. KT handles `|V|=3` *separately* (Lemma
  6.7(i): the triangle realized **directly** by Lemma 5.4, not by splitting). So `|V|=3` needs a **direct
  triangle-realization base case** for the `d=3` molecular conjecture — §1.44's GAP-1 (C) "genuine hole" was
  right; §1.46-(2) shows the easy patch (a `|V|=3` simplicity branch) is *false*, so the hole has no cheap fix.

**Status correction.** Phase 22g does **NOT** have "no research-shaped node remains / ~3–4 routine commits."
Two open items the next session must settle BEFORE the §38-trap producer build:
1. **The `|V|=3` triangle base case** — check whether a direct full-rank/generic realization of the triangle
   (KT Lemma 5.4 / 6.7(i)) is already in the project (base-case machinery near `hbaseGP`) or is new work; if
   new, scope it. This is the genuine sub-problem.
2. **Confirm the `|V|≥4` producer route** sources `hgab` from the GP `.1` conjunct (+ R3 simplicity) and
   composes the GAP-2 upgrade — i.e. re-derive the producer signature with `.1` in the loop (R3 is back ON
   the live route), not the bare-`.2`-only shape §1.46 wrote.

**Process lesson (promote).** A recon that *re-routes* to dissolve a gap (here: "take `.2` instead of `.1`")
must re-verify **every other carried obligation closes under the new route** — §1.46 changed the conjunct the
producer consumes without re-checking the `hgab`/`hnewtrans`/GAP-3 chain that the discarded conjunct fed. The
coordinator's per-commit verdict-reasoning check (coordinate-phase step 3) is what caught it; this is the
general form of that step's anecdote. Lifted to `CLAUDE.md` *Referencing prior work* neighbours / the
coordinate-phase command (this session's instruction-improvement pass).

### 1.48 The §1.47-commissioned recon — (1) the `|V|=3` triangle base case is NEW but bounded work (the green cycle bricks don't assemble; 4 leaves T1–T4, ~3–4 commits); (2) the `|V|≥4` `.1`-in-the-loop wiring CONFIRMS §1.47 as far as it went, but tracing the six-join *dispatch* surfaces **GAP 4**: the `M₃` third-panel candidate (KT's second split `G_a^{vc}` at an *adjacent degree-2 pair*, eqs. (6.41)–(6.44)) is absent from the leaf inventory and inexpressible in the current `hsplit`/`hsplitGP` branch interface (2026-06-09)

> **Build-free design pass; the two §1.47 questions, answered against the Lean and KT read in full.**
> Verified against the green Lean (`theorem_55_base` Pinning.lean:630 — the `V(G)`-relative two-body base;
> `eq_succ_of_isInfinitesimalMotion_cycle`/`isTrivialMotion_of_…`/`rankHypothesis_zero_of_cycle`
> Pinning.lean:670/692/724 — the `Fin m` cycle bricks; `toBodyHinge_rankHypothesis_zero[_cycle]`
> PanelHinge.lean:538/899; `exists_independent_panelSupportExtensor` PanelLayer.lean:445 + the `⋀²`-basis
> plumbing :390/:417; `eq_zero_of_mem_span_singleton_of_sum_eq_zero` RigidityMatrix.lean:2291;
> `isKDof_zero_of_triangle` Deficiency.lean:403; `rank_add_deficiency_eq` Deficiency.lean:1151;
> `exists_degree_eq_two` ReducibleVertex.lean:587 + the reduction's `hsplit` wiring ForestSurgery.lean:1011–1047
> (`splitOff_isMinimalKDof` on the route, :1037); `theorem_55_generic.hsplitGP` PanelHinge.lean:1167–1175;
> `hasGenericFullRankRealization_of_rigidOn_ofNormals` CaseI.lean:1968; `case_III_old_new_blocks_of_line`
> CaseI.lean:3616 (`hL` :3634, `hnewtrans` :3635); `case_III_realization_of_line` :3988 (role-parameterized
> `{v a : α} {e_a : β}`); `case_III_hsplit_producer` :4057; `exists_homogeneousIncidence_of_normals`
> RigidityMatrix.lean:455; `exists_line_data_of_homogeneousIncidence` :582 — the six-join witness-normal
> tabulation) **and KT 2011 read end-to-end at pp. 664 (Lemma 4.6), 677 (Lemmas 6.7/6.8), 680–691 (Lemma 6.10:
> the sketch p. 680 fixing `N_G(v)={a,b}`, `N_G(a)={v,c}`; (6.19)–(6.21) p. 682; the `ρ`-iso + `qρ` p. 686;
> M₁/M₂/M₃ + Claim 6.12 eq. (6.42) p. 690; eqs. (6.43)–(6.44) p. 691)**. No `.lean`/`.tex` edits this pass.

**(1) The `|V|=3` triangle base case — verdict: NEW WORK, bounded (~3–4 commits), and on the critical path
of the whole `hsplit` recursion (not a corner case).** Criticality first: the reduction descends `|V|` by
exactly 1 through `hsplit`, so every split chain that doesn't divert into `hcontract` passes through
`|V|=3`; and the `|V(G)|=4` producer's own GP `.1` conjunct IS the `|V|=3` triangle's GP realization. What
is in tree near `hbaseGP` (the `lem:cycle-realization` thread, partially green):
- `theorem_55_base` (Pinning.lean:630) — the two-body base, already in the right *relative* form
  (`IsInfinitesimallyRigidOn {u,v}`, on ambient `α`), but `m = 2` only.
- The `Fin m` cycle bricks (`rankHypothesis_zero_of_cycle` :724 + its two steps; panel lift
  `toBodyHinge_rankHypothesis_zero_cycle` PanelHinge.lean:899) — the *absolute* `RankHypothesis 0` on body
  type `Fin m`, NOT the `V(G)`-relative motive on `α` the producer needs.
- `exists_independent_panelSupportExtensor` (PanelLayer.lean:445) — supplies `m` **free pairs**
  `(n₁ i, n₂ i)`; a cycle framework's `i`-th support is the *consecutive* pair
  `panelSupportExtensor (normal i) (normal (i+1))` of a SINGLE normal family, so this lemma does **not**
  instantiate the cycle's `hgen`. No cyclically-consistent existence half is in tree.
- No unconditional `hbase`/`hbaseGP` producer exists either (they are still hypotheses, assembled at Leaf 4)
  — so there is no `|V|≤3`-realization machinery to reuse beyond the bricks above.

So: not available; new work. **Decomposition (T1–T4), each bounded, with the landed GAP-2 upgrade as the
keystone that makes T4 cheap** (no triangle-specific genericity work — exhibit ONE rigid seed, upgrade):
- **T1 (graph-side; Operations.lean or Deficiency.lean) — the triangle's third edge + vertex-set pin.**
  `exists_isLink_of_isMinimalKDof_card_three : 3 ≤ bodyBarDim n → G.IsMinimalKDof n 0 → G.Simple →
  V(G).ncard = 3 → G.IsLink eₐ v a → G.IsLink e_b v b → a ≠ v → b ≠ v →
  (a ≠ b ∧ V(G) = {v, a, b} ∧ ∃ f, G.IsLink f a b)`. Route: `a ≠ b` from `G.Simple` + `heab` (a parallel
  pair otherwise); `V(G) = {v,a,b}` from `ncard = 3` + the three distinct members
  (`Set.eq_of_subset_of_ncard_le`); the third edge from the **edge count**: `rank M(G̃) = D(|V|−1) = 2D`
  (`rank_add_deficiency_eq`, `def = 0`) and `rank ≤ |E(G̃)| = (D−1)|E|` force `|E| ≥ ⌈2D/(D−1)⌉ = 3`; on 3
  vertices a simple graph carries at most the three pairs `{v,a},{v,b},{a,b}`, the first two occupied by
  `eₐ/e_b`, so the third edge links `a b`. All inputs green (Phase 19 rank identity; the fiber-count
  plumbing of Deficiency.lean).
- **T2 (rigidity brick; Pinning.lean) — the three-body sibling of `theorem_55_base`.**
  `theorem_55_triangle (F : BodyHingeFramework k α β) {e₁ e₂ e₃ : β} {u v w : α} (huv : u ≠ v)
  (hvw : v ≠ w) (huw : u ≠ w) (hgen : LinearIndependent ℝ ![F.supportExtensor e₁, F.supportExtensor e₂,
  F.supportExtensor e₃]) (h₁ : F.graph.IsLink e₁ u v) (h₂ : F.graph.IsLink e₂ v w)
  (h₃ : F.graph.IsLink e₃ w u) : F.IsInfinitesimallyRigidOn {u, v, w}`. Proof = the
  `eq_succ_of_isInfinitesimalMotion_cycle` telescoping at `m = 3` re-run on `α` (the three relative screws
  lie in the three spans and sum to 0; `eq_zero_of_mem_span_singleton_of_sum_eq_zero` over the `Fin 3`
  `![]`-family forces each to vanish), then the 9-case constancy dispatch of `theorem_55_base`. Stays in
  the relative form, no `Fin m` transport.
- **T3 (concrete seed; PanelLayer.lean) — cyclically-consistent independent joins, `m = 3`.**
  `exists_triangle_normals (k ≥ 1) : ∃ n₀ n₁ n₂ : Fin (k+2) → ℝ, (pairwise LinearIndependent) ∧
  LinearIndependent ℝ ![panelSupportExtensor n₀ n₁, panelSupportExtensor n₁ n₂,
  panelSupportExtensor n₂ n₀]`. Witness: three standard basis vectors; the three joins are the basis
  `⋀²`-family members at `{0,1}, {1,2}, {0,2}` up to the wrap-around sign (`normalsJoin n₂ n₀ = −(n₀∧n₂)`;
  independence survives unit scaling) — `panelSupportExtensor_linearIndependent_iff` +
  `normalsJoin_basisFun_orderEmbOfFin` + `ιMulti_family_linearIndependent_ofBasis`, all green. Needs
  `k+2 ≥ 3`, true at `k = 2`.
- **T4 (assembly; CaseI.lean) — the triangle realization, generic motive.**
  `hasGenericFullRankRealization_of_triangle : … → V(G).ncard = 3 → (T1 data) →
  HasGenericFullRankRealization k G`. Seed `q₀` = T3's normals at `v/a/b` (anything off `{v,a,b}`
  arbitrary), selector `G.endsOf` (`ofNormals_endsOf_recordsLinks` pattern); `hrig` = T2 at the three edges
  (orientation/sign bookkeeping through `endsOf`'s pair order; sign flips don't break `hgen`), rewritten to
  `V(G)` by T1's vertex-set pin; `hne` = every linking edge joins two distinct members of `{v,a,b}` (T1 +
  `G.Simple`), whose seed normals are pairwise independent (T3) — `panelSupportExtensor_ne_zero_iff`. Then
  the landed `hasGenericFullRankRealization_of_rigidOn_ofNormals` concludes the generic motive directly
  (`hends`/`hne`/`hnev`/`hrig` all in hand). This IS KT Lemma 6.7(i)-via-5.4, formalized as the `m=3`
  instance of the cycle realization at an explicit basis seed. *(Note for the bare branch: `hsplit` (no
  `G.Simple`) at `|V|=3` either derives simplicity from `hnoRigid` — a parallel pair or loop is a proper
  rigid subgraph at `|V|=3`, the `splitOff_simple_of_noRigid` argument re-run on `G` itself; KT p. 682 "As
  remarked …, G is a simple graph" — or projects T4's generic conclusion through
  `hasFullRankRealization_of_generic`. One small extra leaf either way, decided at the producer build.)*

**(2) The `|V|≥4` route — the §1.47 `.1`-wiring CONFIRMS, with one addition; but the signature cannot yet
be finalized, because the six-join dispatch trace surfaces GAP 4.**

*Confirmed (the §1.47 route-A chain, every link checked):* R3 `splitOff_simple_of_noRigid_of_card`
discharges the `.1` antecedent at `4 ≤ |V(G)|` → the GP split realization `⟨Q, hQg, hQgp, hQrig, hQlinks,
hQalg⟩ := hIH.1 …` → `hgab := hQgp a b hab` is *definitionally* the placement's
`LinearIndependent ![q(a,·), q(b,·)]` (`ofNormals_normal` rfl, §1.41(2), after the `case_I_realization`-style
`ofNormals`-alignment extraction) → GAP-3's good `t` comes from `hgab` → `hnewtrans`; the line data supplies
`hL`; the candidate completion (`case_III_old_new_blocks_of_line` → `case_III_full_family_of_line` →
`case_III_realization_of_line`) lands the **bare** `HasFullRankRealization 2 G`; the landed GAP-2 upgrade
`hasGenericFullRankRealization_of_rigidOn_ofNormals` re-realizes it generically, its `hne` fed by the IH GP
(the `Gv`-edges) + `hane`/`hnewne` (the `v`-hinges). **Addition (one more reason `.1` is in the loop):** the
producer's N3a triple needs `hn : LinearIndependent ℝ n` for a *triple* — pairwise GP does NOT give triple
independence (`n_c = n_a + n_b` is pairwise-independent). The honest source is the `.1` conjunct's
**`AlgebraicIndependent ℚ`** (an ℝ-linear dependence among three normal rows kills every 3×3 minor, each a
nonzero rational polynomial in the 12 seed coordinates — contradiction). A small bridge leaf
(`linearIndependent_of_algebraicIndependent_normals`, or reuse the det-polynomial route of 22d); KT says
exactly this ("since `(G_v^{ab}, q)` is a generic nonparallel framework, we can take such four points…",
p. 691).

*GAP 4 — the `M₃` third-panel complex (NEW; untracked by §1.40/§1.44/§1.47).* The trace that surfaces it:
- The producer's `pbar` comes from `exists_homogeneousIncidence_of_normals` over a real triple
  `n = ![n_a, n_b, n_c]`, and `exists_line_data_of_homogeneousIncidence`'s tabulation shows the three
  **one-panel joins pin the witness normal to each of the three normals in turn** (`(0,1)↦n 2`,
  `(0,2)↦n 0`, `(0,3)↦n 1`). So every `n u` occurs as the *only* admissible witness normal of some join.
- The placement can realize a witness line **only inside a panel of one of `v`'s graph-neighbours**: the
  candidate hinge is `e_a` (or `e_b`), whose support is `panelSupportExtensor (q₀ v) n_a` — it lies in
  `Π(a)` for *every* choice of `v`'s normal (the seed-from-line core fires only at `n_u = n_a`, role-swap
  `n_u = n_b`). A witness line `L ⊄ Π(a) ∪ Π(b)` is geometrically unplaceable at `v`'s hinges.
- Two panels cannot cover: covering all pairs of 4 points by 2 cliques ("both endpoints in panel `u`")
  forces one panel to contain all 4 points (any point in `A` only and any point in `B` only form an
  uncovered pair) — 4 LI vectors inside one hyperplane of `ℝ⁴`, contradiction. KT states it outright: *"In `d = 2`
  we can show that the corresponding top-left submatrix has full rank in at least one of (6.29) and (6.30),
  but this may not be true for `d ≥ 3`. Hence, we shall introduce another framework `(G,p3)`"* (p. 686).
- **KT's `M₃`** (pp. 680, 686, 690–691): choose `v, a` an **adjacent degree-2 pair** (`N_G(v)={a,b}`,
  `N_G(a)={v,c}` — the sketch's standing choice, from **Lemma 4.6**'s chain-or-cycle dichotomy, p. 664:
  a 2-edge-connected minimal `k`-dof graph with no proper rigid subgraph is a cycle of `≤ d` vertices or
  contains a chain `v₀v₁…v_d` with interior degrees 2; at `d=3` that is *triangle-or-adjacent-pair*). Then
  `G_a^{vc} ≅ G_v^{ab}` by the transposition `ρ = (a v)` (p. 686), and `M₃` is the candidate built on
  `(G_a^{vc}, qρ)` — **the SAME seed `q` transported by `ρ`** — placing the `ac`-hinge at `L'' ⊂ Π(c)`.
  The same-seed bookkeeping is essential: Claim 6.12 tests ONE `r̂`, and eqs. (6.43)–(6.44) (the (6.24)
  dependency read at `a`'s six columns, using that `a`'s only incident edges in `G_v^{ab}` are `ab` and
  `ac` — i.e. `deg(a) = 2`) give `r̂ = −∑ⱼ λ_{(ac)j} rⱼ(q(ac))`, so `M₃`'s candidate row tests the same
  `r̂`. An *independent* IH realization of the second split would break this identity.
- **What is missing in the project** (the GAP-4 leaf list):
  - **G4a — the Lemma-4.6 chain dichotomy** (`d = 3` form): triangle, or an adjacent degree-2 pair `v, a`
    with `N(v) = {a,b}`, `N(a) = {v,c}`, `b ≠ c` (if `b = c` the triangle `{v,a,b}` is a proper rigid
    subgraph at `|V| ≥ 4` — `triangle_isProperRigidSubgraph`, in tree, closes this). The in-tree
    `exists_degree_eq_two` is the *single-vertex* form (avg-degree + the 2-edge-connectivity cut bound);
    the chain strengthening (KT's maximal-chain counting, p. 664) is NOT formalized. New combinatorial
    leaf; its cycle branch is exactly the `|V|=3` triangle of part (1) (cycles of `> 3` vertices have
    adjacent degree-2 pairs trivially).
  - **G4b — the branch interface cannot express the choice.** `minimal_kdof_reduction` picks `v` via
    `exists_degree_eq_two` and hands `hsplit`/`hsplitGP` a FIXED `(v,a,b,eₐ,e_b,e₀)` + the IH value *for
    that split only* (ForestSurgery.lean:1024–1047; PanelHinge.lean:1167–1175). KT's proof needs `v, a`
    *chosen as the adjacent pair* and the second split available. Two repair shapes (decision deferred to
    the next design pass, NOT made here): **(α)** re-point the reduction's degree-2 selection at the
    Lemma-4.6 chain and hand the chain data through the branch (structural edit of
    `minimal_kdof_reduction` + `theorem_55`/`theorem_55_generic` + blueprint nodes; ripples into the
    landed branch consumers); **(β)** hand the `hsplit`/`hsplitGP` branch the **full conditioned IH**
    (mirroring `hcontract`'s shape) and let the producer re-choose its own pair via G4a +
    `splitOff_isMinimalKDof` (in tree, ForestSurgery.lean:1037) — less invasive to the recursion, but the
    branch hypotheses still change shape, and the producer still needs the `ρ`-relabel (G4c) for the
    second split's *same-seed* realization (the full IH cannot substitute — see the (6.44) point above).
  - **G4c — the `ρ`-relabel transport**: a bijective vertex-relabel (transposition) transport for
    `ofNormals` realizations carrying graph/rigidity/links (`G_a^{vc} = ρ-image of G_v^{ab}`, `qρ = q∘ρ`).
    Precedent: Case I's collapse-map transports (G2b `map`-simplicity, G3a rigidity transport) — those are
    harder (non-injective collapse); a bijection is cleaner but is NOT packaged. New leaf.
  - **G4d — the `M₃` candidate-row bookkeeping**: the `(6.24)`-at-`a` column reading
    (`exists_redundant_panelRow_ab_lam`'s combination, restricted to `a`'s columns, + `deg_{G_v^{ab}}(a)=2`
    from the chain) → `r̂ = −∑ λ_{(ac)j} rⱼ(q(ac))` (eq. 6.44), and the `M₃`-candidate `hcand_mem`
    (`hingeRow a c r̂ ∈ span rigidityRows` of the relabeled candidate). Bounded but new; the ab-fiber
    versions are green, the ac-fiber/relabeled versions are not.
  - **G4e — the dispatch leaf**: `hcand`'s trichotomy on the witness join's panel
    (`n_a ↦ M₁` at `e_a`; `n_b ↦ M₂` at `e_b`, roles swapped; `n_c ↦ M₃` via G4c/G4d). The landed
    placement/criterion/C2-feed leaves are role-parameterized and cover M₁/M₂ by instantiation.
- **Why §1.40/§1.44/§1.47 missed it:** §1.40-(2) *named* the M₁/M₂/M₃ trichotomy (including "`M₃`
  (`ac`-split, the `a↔v` iso)") in its fixed-seed analysis, and §1.40-(4) verified the six-join **line
  data** exists for every join — but the leaf decomposition (§1.40-(6), §1.39 Leaf 2/3) silently collapsed
  the dispatch into the single role-parameterized placement, checking data *coverage* without checking
  data *placeability* per witness. Same family as the §1.44/§1.47 lesson: the recon must trace the
  dispatch (which construction consumes each witness), not just that per-witness data exists.

**Combined verdict / corrected remaining-work picture for Phase 22g.** Remaining work =
(i) the `|V|=3` triangle base-case complex T1–T4 (bounded, ~3–4 commits; also the floor of the `hsplit`
recursion); (ii) the GAP-4 `M₃` complex G4a–G4e (multi-commit, with ONE structural decision — G4b (α) vs
(β) — that must be settled by a dedicated design pass *before* the producer signature is final); (iii) the
producer assembly itself (the §38-trap build, composing the confirmed `.1`-chain + GAP-2 upgrade + GAP-3 +
the new triple-LI bridge); (iv) Leaf 4/5 as before. §1.45's "5–6 commits to phase close" and §1.46's
"~3–4 routine commits" are both superseded; the §1.47 "not all-routine" correction stands and widens.
The `|V|≥4` GP-wiring half of §1.47 is **confirmed**; its "buildable" headline was optimistic only in that
it had not yet traced the dispatch. *(ROADMAP §22g note: the opening-recon claim "the path does not consume
`lem:cycle-realization`" needs a caveat — the `|V|=3` base case consumes the green cycle/triangle bricks of
that thread (KT 6.7(i)-via-5.4), though not the red general-`m` node.)*

### 1.49 The GAP-4 interface design pass — G4b verdict **(β)** (hand the no-rigid branch the full conditioned IH, mirroring `hcontract`; KT-faithful and minimal-ripple); G4a–G4e scoped to leaves with signatures; **PLUS GAP 5 surfaced and machine-verified**: `IsProperRigidSubgraph` admits single-vertex subgraphs, so `hnoRigid` is *unsatisfiable* at `|V| ≥ 2` and the reduction's dichotomy is degenerate — the predicate repair (G5) must land before anything else (2026-06-09)

> **The commissioned G4b design pass (docs-only).** Read end-to-end this pass: KT pp. 664–665 (Lemma 4.6
> and its maximal-chain proof), 680–691 (Lemma 6.10 in full: the sketch fixing `N_G(v)={a,b}`,
> `N_G(a)={v,c}`; (6.18)–(6.30); the `ρ`-iso + `qρ` (6.31)–(6.34); the `p₃` row reduction (6.35)–(6.41);
> Claim 6.12 + eqs. (6.43)–(6.45)) — via the `.refs` PDF, not the design notes' paraphrase. Lean read:
> `minimal_kdof_reduction` + `exists_splitOff_data_of_degree_eq_two` (ForestSurgery.lean:923–1047),
> `theorem_55`/`theorem_55_generic` (PanelHinge.lean:1098/1154–1206), `exists_degree_le_two`/
> `exists_degree_eq_two` + `no_rigid_edge_count` (ReducibleVertex.lean:330/495/587),
> `case_III_hsplit_producer` (CaseI.lean:4057), `case_I_realization` (CaseI.lean:2086 — note its explicit
> `hVH2 : 2 ≤ V(H).ncard`), `triangle_isProperRigidSubgraph`/`splitOff_simple_of_noRigid_of_card`
> (Operations.lean:783/833), and `IsRigidSubgraph`/`IsProperRigidSubgraph`/`deficiency`
> (Deficiency.lean:375/381/267). One `lean_run_code` machine-check (the GAP-5 witness below); no `.lean`
> or `.tex` edits this pass.

**(0) GAP 5 — the single-vertex degeneracy of `IsProperRigidSubgraph` (NEW; machine-verified;
blocks the honest dischargeability of BOTH branches).** The finding, with the verified witness:

- `IsProperRigidSubgraph H G n := H.IsRigidSubgraph G n ∧ V(H).Nonempty ∧ V(H) ⊂ V(G)` and
  `IsRigidSubgraph H G n := H ≤ G ∧ H.IsKDof n 0` (Deficiency.lean:375/381). For the single-vertex
  no-edge graph `H = Graph.noEdge {u} β` with `u ∈ V(G)`: `H ≤ G` holds (`{u} ⊆ V(G)` + vacuous
  `isLink_mono`), and `H.deficiency n = ⨆ f, D·(numParts−1) − (D−1)·|crossing| = ⨆ f, D·0 − 0 = 0`
  (every labeling sees one part, no crossing edges), so `H.IsKDof n 0` holds. Hence **for every `G`
  with two distinct vertices, `∃ H, H.IsProperRigidSubgraph G n` is provable.** Verified this session
  by a compiling `lean_run_code` snippet (witness `Graph.noEdge {u} β`; the `IsKDof` computation is
  `partitionDef` + `ciSup_const`, the `⊂` from the second vertex).
- **Consequences.** (i) `hnoRigid : ∀ H, ¬ H.IsProperRigidSubgraph G n` — the standing hypothesis of
  the entire Case-III layer (`no_rigid_edge_count`, `exists_degree_le_two`, `exists_degree_eq_two`,
  `splitOff_isMinimalKDof`, `splitOff_simple_of_noRigid[_of_card]`, `case_III_hsplit_producer`) — is
  **unsatisfiable** whenever `2 ≤ |V(G)|`: those lemmas are true-but-vacuous as stated (none is
  *wrong*; their proofs derive real content from `hnp`, but no caller can ever supply it). (ii) In
  `minimal_kdof_reduction`'s `by_cases hrig`, the negative branch is dead code — the `hsplit` branch
  of `theorem_55`/`theorem_55_generic` is *vacuously dischargeable* (its premises include `hnoRigid`
  together with `v, a ∈ V(G)`, `a ≠ v`). (iii) Dually, `hcontract`'s `∃ H, IsProperRigidSubgraph G n`
  carries **no information**, so the Leaf-4 wiring of `case_I_realization` (which requires
  `hVH2 : 2 ≤ V(H).ncard` — exactly the conjunct the predicate is missing) into `hcontractGP` is
  **undischargeable** for graphs whose only proper rigid subgraphs are singletons (e.g. the
  triangle): the capstone could only close by re-drawing the genuine dichotomy *inside* the
  `hcontract` discharge, abandoning the reduction's split branch entirely — a dishonest dep-graph
  (KT 4.5–4.8/6.10 formalized with unsatisfiable hypotheses) even where technically completable.
- **KT's text has the same surface degeneracy** ("a subgraph `G′` is rigid if `G̃′` contains `D`
  edge-disjoint spanning trees on the vertex set of `G′`", p. 658 — vacuous on one vertex); KT's
  *usage* silently excludes trivial subgraphs (every rigid subgraph KT contracts or counts against
  arises from a matroid circuit, Lemma 3.4, hence has an edge and ≥ 2 vertices). The project wrote
  the definition literally and the degeneracy slipped through; the partial awareness was already on
  record (`ForestSurgery.lean` doc: "a single-vertex subgraph is vacuously rigid so the predicate
  alone does not force the measure to drop") without the unsatisfiability consequence being drawn.
- **Repair (G5) — strengthen the predicate at the definition, not the use sites:**
  `IsProperRigidSubgraph H G n := H.IsRigidSubgraph G n ∧ 2 ≤ V(H).ncard ∧ V(H) ⊂ V(G)`
  (the `Nonempty` conjunct becomes implied; keep or drop). Definition-level, so the *statements* of
  `minimal_kdof_reduction`, `theorem_55`, `theorem_55_generic`, and every `hnp`-consumer are
  textually unchanged; what re-proves is bounded and censused:
  - **Producers of the predicate** (must now also supply `2 ≤ |V(H)|`): the two circuit sites
    `exact hnp (G.inducedSpan n X) ⟨…⟩` (ForestSurgery.lean:734, Operations.lean:334) — a circuit
    spans ≥ 2 vertices *once loops are excluded* (a loop fiber is a rank-0 circuit on one vertex;
    looplessness comes from minimality: a matroid-loop fiber meets no base, contradicting
    `IsMinimalKDof`'s base-meets-every-fiber conjunct — small new brick, or thread an existing
    loopless fact); the triangle sites (Operations.lean:760/765 via `triangle_isProperRigidSubgraph`,
    3 distinct vertices — trivial); `case_I_realization`'s eventual Leaf-4 wiring *gains* `hVH2` for
    free (this is the conjunct it was waiting for).
  - **Blueprint:** `def:rigid-subgraph` (deficiency.tex:105) — add the `≥ 2 vertices` clause + a
    one-line remark on KT's implicit convention. No other node's statement changes.
  - Estimated **1–2 commits**; MUST land before the G4 builds (everything below assumes the genuine
    dichotomy). All §1.44–§1.48 reachability/wiring analyses were implicitly conducted in the
    *corrected* semantics and **stand unchanged** once G5 lands (e.g. "the `|V|=3` triangle is
    reachable in the `hsplit` branch" is true post-G5; pre-G5 nothing reaches `hsplit`).
- *Process note:* the §1.44/§1.47/§1.48 lesson compounds — a recon that traces the route must also
  check the route's *hypotheses are satisfiable*, down to the base predicates. What caught it here
  was reading the producer's branch premises against the *definition* (not the lemma statements)
  while weighing G4b — i.e. exactly the §1.48-commissioned "read the Lean, not the paraphrase".

**(1) G4b — the branch-interface decision: verdict (β), hand the no-rigid branch the full
conditioned IH (mirroring `hcontract`'s shape); the producer chooses its own adjacent pair.**
The two candidates (§1.48(2)): **(α)** re-point `minimal_kdof_reduction`'s degree-2 selection at the
Lemma-4.6 chain and hand `(v,a,b,c,eₐ,e_b,e_c,e₀)` + the split-only IH through the branch; **(β)**
reshape the `hsplit`/`hsplitGP` hypotheses to receive `hnoRigid` + the **full conditioned IH** (as
`hcontract`/`hcontractGP` already do) and let the producer re-choose its pair via G4a +
`splitOff_isMinimalKDof`. Decision factors, weighed against KT and the tree:

1. **KT-faithfulness favors (β).** KT's Lemma 6.10 *is* the full-IH shape: the proof receives the
   induction hypothesis (6.1) — a ∀-over-smaller-graphs statement — invokes Lemma 4.6 *itself* to
   choose the adjacent pair `v, a` (p. 680, the sketch's standing choice), and even applies (6.1) to
   a **second, non-split smaller graph**: Claim 6.11's proof (p. 684) applies (6.1) to
   `G_v = G_v^{ab} − ab` (the `k′ ≤ 4`-dof graph, eq. (6.22)) — KT's split branch was never
   "IH at the one split the recursion hands you". (The project's Claim 6.11 went through the 22d
   rank-polynomial route instead, so *that* IH use is not needed here — but it settles what KT's
   interface is.) The in-file precedent is `hcontract`, which already carries the full conditioned
   IH for exactly this reason (Case I needs the IH at *two* objects, the block and the contraction).
2. **Ripple cost decisively favors (β).** Under (β): `minimal_kdof_reduction` (green, Phase-20,
   blueprint-pinned `thm:minimal-kdof-reduction`) and `theorem_55` (pinned by red `thm:theorem-55`)
   are **untouched**; `theorem_55_generic` has **no blueprint pin and no landed consumers** (Leaf 4
   unbuilt — grep: only doc-comment mentions), so its in-place restate is free; the only landed
   consumer of the old branch shape, `case_III_hsplit_producer`, was *already slated for restate* to
   the `hsplitGP` shape (§1.48's Leaf-3 plan) — zero additional breakage. Under (α): structural edit
   of the closed Phase-20 reduction + both `theorem_55`s + the green `thm:minimal-kdof-reduction` /
   `lem:reducible-vertex` nodes, AND the chain-data tuple freezes into three signatures — any later
   discovery that the producer needs one more datum (this phase surfaced gaps serially: GAPs 1–5)
   re-ripples the whole chain. (β) localizes all future churn in the producer's own hypotheses.
3. **The same-seed constraint is neutral between (α)/(β) — G4c is forced either way.** Eq. (6.44)
   makes `M₃`'s candidate row test the *same* `r̂` only because `(G_a^{vc}, qρ)` is the SAME seed `q`
   transported by `ρ = (a v)` (qρ := q ∘ ρ, (6.31)); Claim 6.12 tests one `r̂` against the three
   panels. So (β)'s full IH must **not** be applied a second time to `G_a^{vc}` (an independent IH
   realization has a different seed, different `λ`s, different `r̂` — the trichotomy collapses);
   the second realization comes from G4c transport, full stop. (α)'s only structural advantage —
   the reduction doing the choosing — buys nothing here.
4. **The triangle arm composes better under (β).** G4a's dichotomy (`|V|=3` triangle vs adjacent
   pair) dispatches *inside* the producer, whose `|V|=3` arm is exactly the already-scoped T1–T4;
   under (α) the reduction would need a fourth branch (`htriangle`) — more reduction surgery for
   the same math.

**Implementation shape (the G4b-impl commit; signatures are design artifacts):** a new ~15-line
sibling induction principle in ForestSurgery.lean — it needs *no* `hD`/`hfresh`/`DecidableEq`
(it constructs no splitOff; pure strong induction + `by_cases hrig`):

```lean
theorem minimal_kdof_reduction_full [Finite α] {n : ℕ} {P : Graph α β → Prop}
    (hbase : ∀ G : Graph α β, G.IsMinimalKDof n 0 → V(G).ncard = 2 → P G)
    (hsplit : ∀ G : Graph α β, G.IsMinimalKDof n 0 → 3 ≤ V(G).ncard →
      (∀ H : Graph α β, ¬ H.IsProperRigidSubgraph G n) →
      (∀ G' : Graph α β, G'.IsMinimalKDof n 0 → 2 ≤ V(G').ncard →
        V(G').ncard < V(G).ncard → P G') → P G)
    (hcontract : ∀ G : Graph α β, G.IsMinimalKDof n 0 → 3 ≤ V(G).ncard →
      (∃ H : Graph α β, H.IsProperRigidSubgraph G n) →
      (∀ G' : Graph α β, G'.IsMinimalKDof n 0 → 2 ≤ V(G').ncard →
        V(G').ncard < V(G).ncard → P G') → P G) :
    ∀ G : Graph α β, G.IsMinimalKDof n 0 → 2 ≤ V(G).ncard → P G
```

then restate `theorem_55_generic`'s `hsplit`/`hsplitGP` to mirror `hcontract`/`hcontractGP` verbatim
(premises `hG`/`hV3`/`hnoRigid`[/`G.Simple` for GP] + the full conditioned IH), rewire its proof over
the new principle (the wiring lambda at PanelHinge.lean:1198–1201 simplifies), and drop its now-unused
`hD`/`hfresh` (linter; Leaf 4 adjusts — unconsumed today). `theorem_55` (bare) keeps the old shape and
the old reduction — it is the general-`d`/narrative node; the `d=3` route consumes only
`theorem_55_generic` (Leaf 4 projects `.2`, R2 §1.41). The degree-2 selection machinery
(`exists_degree_eq_two`, `exists_splitOff_data_of_degree_eq_two`, `splitOff_isMinimalKDof`,
`splitOff_vertexSet_ncard_lt`) all remain consumed — by the *producer* now (and by the untouched bare
reduction). Blueprint: a small green node for the new principle (or fold into the
`thm:minimal-kdof-reduction` prose as its trivial full-IH corollary); `lem:case-II-realization` (red)
restates its branch-shape prose in the producer commits.

**(2) G4a — the `d = 3` chain dichotomy (adjacent degree-2 pair), with a CHEAPER proof than KT's
maximal-chain counting.** KT Lemma 4.6 at `d = 3` needs a chain `v₀v₁v₂v₃` with
`deg(v₁) = deg(v₂) = 2` — i.e. an **edge whose two endpoints both have degree 2**. KT's proof
(pp. 664–665) counts maximal chains; at `d = 3` (`D ≥ 6`) a two-line double count suffices and avoids
formalizing chains entirely. Suppose no such edge: then the 2s edge-ends at `X₂ := {deg = 2}` pair
with ends in `X₃₊`, so `Σdeg ≥ 2s + 2s = 4s` (s := |X₂|; loops at degree-2 vertices are excluded as
in `exists_splitOff_data_of_degree_eq_two`), and `Σdeg ≥ 2s + 3t` (t := |X₃₊|; `X₀ = X₁ = ∅` by
two-edge-connectivity). Against the green KT-4.5 bound (`no_rigid_edge_count`,
`(D−1)Σdeg < 2D|V| − 2`): from `Σdeg ≥ 2s+3t` get `(D−3)t < 2s`; from `Σdeg ≥ 4s` get
`(D−2)s < Dt`; composing, `(D−2)(D−3)t < 2Dt` — false for `D ≥ 6` (at `D = 6`: `12t < 12t`),
contradiction (`t = 0` separately: no `X₂`–`X₂` edge then means no edges at all). Two leaves,
both in ReducibleVertex.lean (which already imports Operations via SplitOffDeficiency, so
`triangle_isProperRigidSubgraph` is reachable):

- **G4a-i (the counting core):** `theorem exists_adjacent_degree_two_pair [DecidableEq β] [Finite α]
  [Finite β] {G : Graph α β} {n : ℕ} (hD : 6 ≤ bodyBarDim n) (hV : 3 ≤ V(G).ncard)
  (hG : G.IsMinimalKDof n 0) (hnp : ∀ H, ¬ H.IsProperRigidSubgraph G n) :
  ∃ v a, v ∈ V(G) ∧ a ∈ V(G) ∧ G.degree v = 2 ∧ G.degree a = 2 ∧ ∃ e, G.IsLink e v a` —
  the double count above over `handshake_degree_subtype` + `no_rigid_edge_count` + the degree-`= 2`
  upgrade (`two_le_crossingEdges_of_isKDof_zero` per vertex, as in `exists_degree_eq_two`).
  Note the **`hD : 6 ≤ bodyBarDim n`** (the `d = 3` regime; KT's general-`d` chain needs the
  maximal-chain argument — Phase 23, where the chain form generalizes).
- **G4a-ii (the chain-data extraction, `|V| ≥ 4`):** `theorem exists_chain_data_of_noRigid … (hV4 :
  4 ≤ V(G).ncard) … : ∃ (v a b c : α) (eₐ e_b e_c : β), v ∈ V(G) ∧ a ∈ V(G) ∧ b ∈ V(G) ∧ c ∈ V(G) ∧
  a ≠ v ∧ b ≠ v ∧ b ≠ a ∧ c ≠ v ∧ c ≠ a ∧ b ≠ c ∧ eₐ ≠ e_b ∧ eₐ ≠ e_c ∧ G.IsLink eₐ v a ∧
  G.IsLink e_b v b ∧ G.IsLink e_c a c ∧ (∀ e x, G.IsLink e v x → e = eₐ ∨ e = e_b) ∧
  (∀ e x, G.IsLink e a x → e = eₐ ∨ e = e_c)` — from G4a-i + `exists_splitOff_data_of_degree_eq_two`
  run at `v` *and* at `a` (reconciling the shared edge `eₐ`); `b ≠ a`/`c ≠ v` since a second
  `va`-edge is a parallel pair (kills `G.Simple`, below); **`b ≠ c` via
  `triangle_isProperRigidSubgraph` + `hnp`** (a `b = c` collapse makes `G[{v,a,b}]` a proper rigid
  subgraph at `|V| ≥ 4`). Consumes the simplicity leaf **G0**: `theorem simple_of_isMinimalKDof_of_
  noRigid … (hV : 3 ≤ V(G).ncard) … : G.Simple` (KT p. 682 "As remarked…, G is a simple graph";
  parallel pair ⟹ the 2-vertex double-edge `K₂` is a proper rigid subgraph at `|V| ≥ 3` — needs the
  small `K₂`-is-0-dof partition brick, sibling of `isKDof_zero_of_triangle`; loop ⟹ matroid-loop
  fiber meets no base ⟹ contradicts minimality — shared with G5's circuit-site repair). G0 also
  discharges the producer's bare-conjunct projection (§1.48 T4 note, now pinned here).

**(3) G4c — the `ρ`-relabel transport at a FIXED seed (not the existential motive).** What the
producer needs is the concrete-level transport: the IH realization is
`ofNormals (G.splitOff v a b e₀) ends₁ q₀` with (rigidity on `V∖{v}`, GP, `AlgebraicIndependent ℚ`,
links); `M₃` needs the SAME data on `G.splitOff a v c e₁` at seed `q₀ ∘ ρ`, `ρ = Equiv.swap a v`.
Transporting the *existential* `HasGenericFullRankRealization` would lose the seed identity that
(6.44) requires — state everything at the `ofNormals` level. Two leaves:
- **G4c-i (graph side; Operations.lean):** the iso. With the chain data and fresh `e₀ ∉ E(G)`,
  `e₁ ∉ E(G) ∪ {e₀}`: `(G.splitOff a v c e₁).IsLink e x y ↔ (G.splitOff v a b e₀).IsLink (σ e)
  (ρ x) (ρ y)` where `σ = Equiv.swap e_b e₀ * Equiv.swap e₁ e_c` and `ρ = Equiv.swap a v`
  (checked against KT (6.31): surviving `e ∉ {eₐ,e_b,e_c}` fixes both; `e_b ↦ e₀` carries `vb ↦ ab`;
  `e₁ ↦ e_c` carries `vc ↦ ac`; needs `b ≠ c` and the two closures — all G4a-ii data). Note the
  freshness plumbing: `e₁` must avoid `E(G) ∪ {e₀}`, which `hfresh G` alone does not give — apply
  `hfresh` to a graph carrying `E(G) ∪ {e₀}` (e.g. `G.splitOff v a b e₀ ∪ G` or an `addEdge`), a
  small definitional detour to settle at build time.
- **G4c-ii (framework side; PanelLayer/CaseI.lean):** relabel-invariance of `ofNormals` data under a
  vertex `Equiv` + edge `Equiv` intertwining `IsLink`: rigidity-on-`V` transports (precompose
  motions with `ρ⁻¹`; the rigidity matrix's columns permute), `rigidityRows` correspond under the
  dual of the `ρ`-permutation iso (the row-space correspondence G4d consumes), the links/`ends`
  selector composes, and the GP/`AlgebraicIndependent ℚ` conjuncts are **free** (the coordinate
  *set* of the seed is unchanged — `(q₀ ∘ ρ)`'s coordinate family is `q₀`'s reindexed;
  `AlgebraicIndependent.comp ρ` + the GP pairwise statement reindexes). Precedent: the Case-I
  collapse transports (G2b/G3a) are the *harder* non-injective versions; a bijection is cleaner but
  is genuinely not packaged. Bounded plumbing, no new math.

**(4) G4d — the eq.-(6.43)/(6.44) `a`-column bookkeeping (the `M₃` candidate row).** From the green
ab-fiber dependency (`exists_redundant_panelRow_ab_lam`: `r̂ = Σ_j λ_j r_j`, `λ_{i*} = 1`, over the
`e₀`-fiber + `E_v` rows of the split framework), read the six `a`-columns (evaluate the row
functionals at `single a S`): rows of edges not incident to `a` vanish, and `a`'s only `G_v^{ab}`
edges are `e₀` (the fresh `ab`) and `e_c` (the surviving `ac`) — `deg_{G_v^{ab}}(a) = 2` from the
chain closures. Result (6.44): `r̂∘(single a) = −Σ_j λ_{(ac)j} r_j(q(ac))∘(single a)` — as a
functional identity, `r̂ = −Σ_j λ_{(ac)j} rⱼ(C(e_c-hinge))` in the project's row terms. Two pieces:
- **G4d-i (the column reading; CaseI.lean, abstract `F`):** the `(6.43) → (6.44)` identity from the
  dependency + the two-edges-at-`a` closure. Mirrors the `exists_redundant_panelRow_ab_lam` fiber
  bookkeeping at the `ac`-fiber; bounded.
- **G4d-ii (the `M₃` `hcand_mem`):** `hingeRow a c r̂ ∈ span rigidityRows` of the `p₃` candidate
  framework (the relabeled `ofNormals` of G4c with the `ac`-hinge placed at the witness line
  `L″ ⊂ Π(c)`), via G4d-i + `hingeRow_mem_rigidityRows` + G4c-ii's row correspondence — the
  `M₃` analogue of the landed `hcand_mem` route (§1.35). The `(6.35)–(6.41)` matrix reduction of KT
  is *not* re-formalized: the project's row-space criterion + `case_III_old_new_blocks_of_line` at
  the `(a,c)` role instantiation replaces it (role-parameterization confirmed: `case_III_realization_
  of_line` is `{v a : α} {e_a : β}`-generic, CaseI.lean:3988).

**(5) G4e — the witness-panel dispatch trichotomy (the producer's `hcand` body, not a standalone
node).** `exists_line_data_of_homogeneousIncidence` tabulates each witness join's admissible normal
`n_u ∈ {n_a, n_b, n_c}` (= the split-seed normals `q₀ a, q₀ b, q₀ c` after the N3a instantiation).
Dispatch: `n_a ↦ M₁` (candidate at `eₐ`, the landed placement/criterion/C2-feed chain), `n_b ↦ M₂`
(same chain, roles `a ↔ b` swapped — landed, instantiation only), `n_c ↦ M₃` (the second split:
G4c transport of the SAME seed + G4d candidate row + the same landed completion chain at `(a,c)`).
All three arms end in the bare `HasFullRankRealization 2 G` → the landed GAP-2 upgrade. G4e is the
`rcases` spine inside the restated producer; its only new content is the three-way case split on
the line-data witness normal (a `Fin 3`-valued discriminator worth a small helper lemma).

**(6) Build order (supersedes §1.48's "combined verdict" sequencing; T1–T4 remain parallel-safe):**
1. **G5** — the predicate repair + consumer re-proofs (1–2 commits; BLOCKS everything; includes the
   loopless-from-minimality brick shared with G0).
2. **G4b-impl** — `minimal_kdof_reduction_full` + the `theorem_55_generic` restate (1 commit; pins
   the producer signature).
3. **G4a-i/G4a-ii + G0** (1–2 commits) ∥ **T1–T4** (§1.48(1), ~3–4 commits) ∥ **G4c-i/G4c-ii**
   (1–2 commits) — mutually independent once G5/G4b-impl land.
4. **G4d-i/G4d-ii** (1–2 commits; consumes G4c).
5. **The producer assembly** (the §38-trap build): restate `case_III_hsplit_producer` to the (β)
   branch shape; body = G4a choice → `|V|=3 ↦ T4` / chain ↦ {IH at the `v`-split (via
   `splitOff_isMinimalKDof` + measure), R3 → `.1` → `hgab` + triple-LI bridge, GAP-3 good-`t`,
   G4e dispatch with M₃ via G4c/G4d} → GAP-2 upgrade; bare conjunct via G0 +
   `hasFullRankRealization_of_generic` (1–2 commits).
6. **Leaf 4** (`theorem_55_generic (n:=2) (k:=2)` instance, `.2` projection — now over the (β)
   shape, and the `hcontractGP` wiring gains `hVH2` from G5) + **Leaf 5** as before.

### 1.50 The `hcand`-discharge recon — the discriminator restate is a free statement-level change; the §1.49(5) M-arm route as scoped is NOT dischargeable (the sheared placement breaks KT's (6.26)–(6.28) row transport — surfaced and DISSOLVED via the KT-Lemma-5.2 rank-transfer re-route: certify at the `t = 0` hinge-level family, transfer along the one-parameter shear); **PLUS GAP 6 surfaced (genuinely open)**: the eq.-(6.22) rank lower bound at the `k'`-dof `G_v` is KT's nested IH (6.1), which the project's 0-dof-only induction cannot supply (2026-06-10)

> **Docs-only recon (the §1.49(5) build-out design pass).** Lean read this pass (declarations, not
> paraphrases): `exists_line_data_of_homogeneousIncidence` (RigidityMatrix.lean:582, incl. both
> builders), `exists_complementIso_ne_zero_of_homogeneousIncidence` (:1984), `case_III_claim612`
> (:1843), `candidateRow_ac_eq_neg` (:1790), `exists_homogeneousIncidence_of_normals` (:455),
> `annihRow` (PanelLayer.lean:800 — **linear in `C`**, load-bearing below),
> `exists_shear_linearIndependent_pair` / `panelSupportExtensor_add_smul_left_ne_zero_of_join_ne_zero`
> (PanelLayer.lean:363/332), and in CaseI.lean: `case_III_hsplit_producer` (:4256, the `hcand`
> application site :4334), `case_III_old_new_blocks[_of_line]` (:3443/:3619),
> `case_III_full_family_of_line` (:3800), `case_III_realization_of_line` (:3991),
> `exists_redundant_panelRow_ab_{of_finrank_eq,decomposition[_acolumn_zero],lam}` (:3093–:3300),
> `exists_candidate_row_eq612` (:3374), `hasGenericFullRankRealization_of_rigidOn_ofNormals`
> (:1971), `ofNormals_relabel`/`rigidityRows_ofNormals_relabel` (:4379/:4517), G4d-i/ii
> (:4659/:4727), the triple-LI bridge (:4767); the rank-side suppliers
> `finrank_infinitesimalMotions_of_isInfinitesimallyRigidOn_vertexSet` /
> `exists_independent_panelRow_subfamily_of_rigidOn[_linking]` (GenericityDevice.lean:431/521/603,
> incl. the inline `hfin` rank-nullity block), `rankHypothesis_ofNormals_of_rankPolynomial_
> algebraicIndependent` (CaseI.lean:2723 — note its `hspan : V(G) = univ`),
> `splitOff_removeVertex_minimalKDof` (ForestSurgery.lean:2042), `theorem_55[_generic]`
> (PanelHinge.lean:1098/1154). KT read: pp. 668–669 (Lemma 5.2 **in full** — the rotation
> `Π_t(a)`, minors continuous in `t`), 681–686 (the p₁/p₂/p₃ sketch; eqs. (6.12), (6.16),
> (6.19)–(6.21), Claim 6.11 + footnote 6, eqs. (6.22)–(6.30)). No `.lean`/`.tex` edits this pass.

**(a) The witness-normal discriminator — verdict: BUILDABLE, a statement-level restate of both
lemmas in place (proofs reuse verbatim).** Both builders inside
`exists_line_data_of_homogeneousIncidence` already return a *real* normal: `hone` yields
`⟨n u, n', …⟩` and `htwo` yields `⟨n u, n w, …⟩` — the bound `n_u` is `n u` in every one of the six
`fin_cases` branches (per-join `u`: `(0,1)↦2, (0,2)↦0, (0,3)↦1, (1,2)↦0, (1,3)↦1, (2,3)↦0`).
Neither lemma has any consumer outside RigidityMatrix.lean (grep), so both are restated **in
place** at the discriminating level:

```lean
theorem exists_line_data_of_homogeneousIncidence
    {n : Fin 3 → Fin 4 → ℝ} (hn : LinearIndependent ℝ n)
    {pbar : Fin 4 → Fin 4 → ℝ}
    (h0 : ∀ u, pbar 0 ⬝ᵥ n u = 0)
    (h1 : pbar 1 ⬝ᵥ n 0 = 0 ∧ pbar 1 ⬝ᵥ n 1 = 0)
    (h2 : pbar 2 ⬝ᵥ n 1 = 0 ∧ pbar 2 ⬝ᵥ n 2 = 0)
    (h3 : pbar 3 ⬝ᵥ n 2 = 0 ∧ pbar 3 ⬝ᵥ n 0 = 0) :
    ∀ q : {q : Fin 4 × Fin 4 // q.1 < q.2},
      ∃ (u : Fin 3) (n' pi pj : Fin 4 → ℝ), LinearIndependent ℝ ![n u, n'] ∧
        pi ⬝ᵥ n u = 0 ∧ pi ⬝ᵥ n' = 0 ∧ pj ⬝ᵥ n u = 0 ∧ pj ⬝ᵥ n' = 0 ∧
        omitTwoExtensor pbar (ne_of_lt q.2) = extensor ![pi, pj]

theorem exists_complementIso_ne_zero_of_homogeneousIncidence
    {r : Module.Dual ℝ (ScrewSpace 2)} (hr : r ≠ 0)
    {pbar : Fin 4 → Fin 4 → ℝ} (hp : LinearIndependent ℝ pbar)
    {n : Fin 3 → Fin 4 → ℝ} (hn : LinearIndependent ℝ n)
    (h0 …h3 : as above) :
    ∃ (u : Fin 3) (n' : Fin 4 → ℝ), LinearIndependent ℝ ![n u, n'] ∧
      r (complementIso (k := 2) (j := 2) (by omega)
        ⟨extensor ![n u, n'], extensor_mem_exteriorPower _⟩) ≠ 0
```

The producer instantiates `n := ![n_a, n_b, n_c]` (the triple-LI bridge's exact output family), so
the discriminator dispatch is `u = 0 ↦ M₁(Π(a)), 1 ↦ M₂(Π(b)), 2 ↦ M₃(Π(c))`. One commit.

**(b) The `h618`/`h622` rank inputs — `h618` is a micro-leaf; `h622` is GAP 6, genuinely open.**
At the `hcand` application site (CaseI.lean:4334) the discharge lemma may consume, beyond `hcand`'s
own parameters: `hD`, `hG`, `hV4'`, `hnoRigid`, `hsimple`, `hfresh`, `hGv` (split minimal 0-dof),
`hGvSimple`, **and `hIH` (the full conditioned IH — but over minimal `0`-dof graphs ONLY)** — all
in scope where the producer applies `hcand`, hence suppliable by the Leaf-4 wiring lambda.

- **h618 (eq. (6.18), the split's full rank at the IH seed): LANDED (W2, GenericityDevice.lean).**
  The packaged lemma below (`finrank_span_rigidityRows_of_rigidOn`) extracts the inline `hfin` block
  (was GenericityDevice.lean:543/630); the two `…_subfamily_of_rigidOn`(`_linking`) sites now call it.
  Placed in GenericityDevice (beside its dependency `finrank_infinitesimalMotions_of_…_vertexSet`),
  not RigidityMatrix as aspired below — the support lemma is downstream of RigidityMatrix. Signature:

  ```lean
  theorem BodyHingeFramework.finrank_span_rigidityRows_of_rigidOn [Finite α]
      (F : BodyHingeFramework k α β) (hnev : F.graph.vertexSet.Nonempty)
      (hrig : F.IsInfinitesimallyRigidOn F.graph.vertexSet) :
      Module.finrank ℝ (Submodule.span ℝ F.rigidityRows)
        = screwDim k * (F.graph.vertexSet.ncard - 1)
  ```

  (`infinitesimalMotions_eq_dualCoannihilator` + `finrank_infinitesimalMotions_of_…_vertexSet` +
  the dual-annihilator complement + `finrank_screwAssignment`; no `hends`/`hne` needed at this
  level.) Instantiated at the unpacked IH framework (the `hQeq` re-expression idiom of
  `hasGenericFullRankRealization_of_splitOff_relabel`), with `m := V(G.splitOff v a b e₀).ncard`.
- **h622 (eq. (6.22)) — first, the consumer-side reduction.** `exists_redundant_panelRow_ab_lam`'s
  `h622`-equality is over-strong: define `k'' := D(m−1) − finrank ℝ (span ℝ (Gv-rows))` with
  `Gv := G.removeVertex v` (its links = the split's minus `e₀`, so `hle`/`hsplit` hold); then
  `h622` holds *by construction* once `finrank (Gv-rows) ≤ D(m−1)` (free: `span_rigidityRows_eq_
  sup_span_panelRow_edge` + h618 + monotonicity), and the whole remaining content is the single
  `hk'`-feeding inequality

  ```lean
  -- GAP 6 — the ONE open analytic input (KT eq. (6.22) lower bound, nested IH (6.1) at G_v):
  screwDim k * (m - 1) - (screwDim k - 2)
    ≤ Module.finrank ℝ (Submodule.span ℝ
        (PanelHingeFramework.ofNormals (G.removeVertex v) ends q).toBodyHinge.rigidityRows)
  ```

  at the IH's alg-indep seed `q`. **This is NOT derivable from anything landed.** KT derives it by
  applying the induction hypothesis (6.1) to the **minimal `k'`-dof** graph `G_v` (`k' ≤ D−2` is
  the landed gap3 `splitOff_removeVertex_minimalKDof`) and transferring to the fixed seed by
  footnote 6 — the landed seed-rank kernel (`finrank_infinitesimalMotions_le_of_rankPolynomial_
  algebraicIndependent`, usable here, no `hspan`) consumes a **rank-polynomial witness for `G_v`**
  that only a `k'`-dof realization theorem can produce. The project's induction motive
  (`theorem_55[_generic]`, `minimal_kdof_reduction[_full]`, the producer's `hIH`) is **0-dof
  only**; `G_v` has `k' > 0` in general. Verified dead ends: (i) the deterministic hub bound runs
  the wrong way (`rank ≤ D(m−1) − k'`); (ii) augmenting `G_v` to a 0-dof graph and restricting
  loses up to `D−1` per added fiber (only recovers the trivial `≥ D(m−1) − (D−1)`, one short);
  (iii) the row-level "added rank ≤ matroid added rank" increment bound is false deterministically.
  Also: the landed packaging `rankHypothesis_ofNormals_of_rankPolynomial_algebraicIndependent`
  carries `hspan : V(G) = Set.univ`, unsatisfiable in the producer context (ambient junk bodies +
  the removed `v`) — the reduced-inequality form above is the right consumer-level target, fed
  through the (no-`hspan`) upper-bound lemma once a witness exists. **Resolution options** (needs
  coordinator/user adjudication): **(i)** strengthen the induction to KT's actual all-`k` motive
  (KT 5.5 inducts over minimal `k`-dof for all `k`; the `k ≥ 1` split arm is *easier* — the landed
  22c one-short brick already meets the `k ≥ 1` target — but this restructures the Phase-20
  reduction + `theorem_55[_generic]` + base/contract cases: phase-sized); **(ii)** carry the GAP-6
  inequality as the explicit `h…` crux (the standing Phase-21b idiom) on the redundancy-data leaf
  and let it ride up through the discharge to the Leaf-4/5 wiring — 22h then closes green-modulo
  one honestly-named hypothesis, discharged by a successor sub-phase implementing (i). **(ii) is
  the recommended interim**: it unblocks every other leaf and isolates the genuine residue.

**(c) The M₁ arm — the §1.49(5)/§1.40(6) route as scoped is NOT dischargeable (surfaced flaw),
and DISSOLVES via the KT-Lemma-5.2 rank-transfer re-route.**

- **The flaw (machine-checked against the Lean + KT pp. 681–686).** KT's eq.-(6.12) candidate `p₁`
  places **both** `p₁(va) = L ⊂ Π(a)` (the free witness line) **and** `p₁(vb) = q(ab)` (the
  `vb`-hinge *at* the IH `ab`-hinge — the row-transport (6.26)–(6.28) and the (6.29) bottom block
  both live on this reproduction). That forces `v`'s panel `= Π(a)`, which `ofNormals` cannot
  represent non-degenerately (equal normals kill the `va`-support). The project's sheared seed
  `q₀(v) = n_a + t•n'` (`t ≠ 0`) keeps `va = L` but moves the `vb`-hinge to
  `C_new = C(e₀) + t • panelSupportExtensor n' n_b ≠ C(e₀)`: the transported `(vb)ⱼ`-functionals
  `hingeRow v b ρⱼ` (`ρⱼ ∈ (span C(e₀))^⊥`) are then **not** rows of the sheared candidate
  (`ρⱼ(C_new) = t·ρⱼ(panelSupportExtensor n' n_b) ≠ 0` in general), so `case_III_realization_of_
  line`'s `hro_mem` (the OLD block's `e₀`-fiber members) and `hcand_mem` are **undischargeable at
  the sheared `ofNormals` placement** for `n' ≠ n_b` — and at `n' = n_b` the gate `r̂(C(e_a)) ≠ 0`
  is identically false (`C(e_a) = (−t)C(e₀)` and `r̂(C(e₀)) = 0` by construction). Moreover the
  `hold`-shaped (v-vanishing) OLD block of `case_III_{full_family,realization}_of_line` caps at
  `D(m−1) − 1` certifiable dimensions at any non-degenerate line (the in-span v-vanishing subspace
  is `Gv`-span + the codim-1 `ab`-slice `(C(e₀))^⊥ ∩ (C(L))^⊥`), one short of its `hcard` — KT's
  (6.29) bottom block is *not* v-vanishing; it is **restriction-independent** (the `(vb)ⱼ`-rows
  restricted to `V∖{v}` reproduce the split's rows after the column op). Both landed `_of_line`
  leaves stay as reusable infrastructure (blocks, transversality, criterion), but their
  OLD-contract is the wrong shape for the live route.
- **The dissolution = KT Lemma 5.2, made one-variable-polynomial (pp. 668–669: rotate `Π_t`,
  "each minor of `R(G, p_t)` is continuous in `t`").** Certify the full count at the **`t = 0`
  hinge-level family** and transfer along the shear:
  * **`F₀` — KT's `p₁` as a `BodyHingeFramework`** (hinge-primary, no normals needed):
    `F₀.graph = G`, `supportExtensor: e_a ↦ panelSupportExtensor n_a n' (= C(L)), e_b ↦
    panelSupportExtensor n_a n_b (= C(e₀)), e ↦ the split's extensor otherwise`. At `F₀` every
    (6.26)–(6.28) membership holds **by construction**: `ρⱼ ∈ F₀.hingeRowBlock e_b` literally, so
    the transported `(vb)ⱼ`-rows are genuine `F₀`-rows, and the operated candidate row (the (6.28)
    pure-`v` row with value `r̂`) is a span-member as an explicit combination — no shear identity
    needed (`exists_candidate_row_eq612`'s argument, easier).
  * **The certifying family `g : ℝ → ι → Module.Dual ℝ (α → ScrewSpace k)`** over a fixed index
    `ι` of size `D(|V(G)|−1)`: the `e_a`-members are `hingeRow v a (annihRow C(L) t₁ t₂)` —
    **constant in `t`**, and since `annihRow` is linear in its extensor (PanelLayer.lean:800),
    each equals `(−1/t) •` a genuine `panelRow` of the sheared candidate for every `t ≠ 0`; all
    other members are genuine `panelRow`s of `ofNormals G ends (q₀ t)` (`q₀ t = q` off `v`,
    `v ↦ n_a + t•n'`) — polynomial in `t`. `g 0` is the `F₀`-certified KT-(6.29) family; for
    `t ≠ 0` every member lies in `span (sheared candidate).rigidityRows`.
  * **The transfer leaf (B)**: `LinearIndependent ℝ (g 0)` + entrywise polynomiality ⟹
    independent for all but finitely many `t` (coordinatize `Module.Dual ℝ (α → ScrewSpace k)`;
    a top minor is a `Polynomial ℝ`, nonzero at `0`); intersect with
    `exists_shear_linearIndependent_pair`'s ≤ 1 bad value to pick a good `t ≠ 0` with every
    linking hinge transversal. Then `hasFullRankRealization_of_independent_rigidityRow` (landed)
    gives the bare realization and `hasGenericFullRankRealization_of_rigidOn_ofNormals` (GAP-2,
    landed) the generic motive. Note: the witness gate consumed at `t = 0` is `r̂(C(L)) ≠ 0` —
    the discriminator glue's output composed with `panelSupportExtensor_eq_complementIso_extensor`
    directly; the previously-planned sheared-support step
    (`panelSupportExtensor_add_smul_left_ne_zero_of_join_ne_zero` feed) is **obsolete** under the
    re-route (the shear factor never meets the gate).
  * **New leaves** (shapes; exact forms pinned at build):
    - **A0 (restriction-bottom block-triangular augment; the missing sibling of the landed
      v-vanishing augment):** `Sum.elim top bot` independent when the `top` rows are pure-`v`
      (post-columnOp) with pinned-independent `v`-forms and the `bot` rows' restrictions to
      `V∖{v}` are independent. (Proof skeleton: evaluate a vanishing combination on `v`-vanishing
      assignments to kill `bot`, then pin `v`.)
    - **B (one-variable rank transfer; graph-free):**
      `∀ {ι κ} [Fintype ι] (b : Basis κ ℝ M) (g : ℝ → ι → M) (P : ι → κ → Polynomial ℝ)
      (hg : ∀ t i j, b.repr (g t i) j = (P i j).eval t) (h0 : LinearIndependent ℝ (g 0))
      (bad : Finset ℝ) : ∃ t, t ∉ bad ∧ t ≠ 0 ∧ LinearIndependent ℝ (g t)`.
    - **A1 (the `t = 0` certification, per arm):** assemble `g 0` independent at `F₀` from: the
      redundancy data (`exists_redundant_panelRow_ab_lam`'s `r`/`lam`/`i` + `h618` + the (b)
      `k''`-reduction, with the GAP-6 inequality as an explicit hypothesis pending adjudication),
      the witness gate `r̂(C(L)) ≠ 0`, A0, and the landed columnOp/criterion bricks. The bottom is
      the chosen `D(m−1)` independent split-rows-minus-`(ab)i*` carried as `F₀`-rows (`Ev`-rows
      verbatim; `(ab)ⱼ ↦ (vb)ⱼ`).
    - **A2 (the arm closer):** A1 + B + the membership packaging + the device feed + GAP-2 ⟹
      `HasGenericFullRankRealization 2 G`.
  Verdict: **buildable modulo GAP 6** (carried per (b)(ii)); the count, memberships, and transfer
  were each re-verified against KT (6.16)/(6.23)/(6.29) and the landed signatures.

**(d) M₂ — CONFIRMED a roles-`a↔b` instantiation of the M₁ chain; nothing new.** Same split, same
`e₀`, same `r̂` (KT p. 681: "`r′` is indeed equal to `r`"): candidate hinge `e_b` at `L' ⊂ Π(b)`
(`u = 1` witness), reproduced hinge `e_a` at `C(e₀)`, shear `q₀'(v) = n_b + t•n''`, `F₀`/`g`/A0–A2
verbatim at the swapped roles. The good-`t` input swaps `hgab` to `![n_b, n_a]`
(`LinearIndependent` swap, derivable from GP/the triple-LI bridge).

**(e) M₃ — same A0/A1/B pattern at the relabeled `a`-split; G4c/G4d thread as inputs, plus the
landed sign bridge.** The chain, named: **(1)** `ofNormals_relabel` (G4c-ii, fixed seed) turns the
unpacked `v`-split IH data into the rigid `a`-split framework
`ofNormals (G.splitOff a v c e₁) endsσρ qρ` at the same seed values (`qρ(a,·) = n_v… = q₀∘ρ`;
`e₁` fresh via `hfresh` applied to a graph carrying `E(G) ∪ {e₀}`, the §1.49(3) freshness
plumbing); the (b) micro-leaf `finrank_span_rigidityRows_of_rigidOn` then gives the `M₃` `h618`
analogue at the relabeled framework. **(2)** The `t = 0` candidate `F₀''` re-inserts `a`: graph
`G`, `supportExtensor: e_c ↦ panelSupportExtensor n_c n''' (= C(L''), L'' ⊂ Π(c), the `u = 2`
witness), e_a ↦ panelSupportExtensor n_a n_c (the relabeled split's `e₁ = vc`-hinge, the
reproduction `p₃(av) = qρ(vc)`), e ↦ the `a`-split's extensor otherwise`; the shear is
`q₀''(a) = n_c + t•n'''`. **(3)** The candidate row's value is the **same** `r̂` with reversed
sign: `candidateRow_ac_eq_neg` (RigidityMatrix.lean:1790, landed) consumes the `a`-column
vanishing of the (6.24) combination (`exists_redundant_panelRow_ab_decomposition_acolumn_zero`,
landed) regrouped at the degree-2 body `a` — the regrouping's `grest`-vanishing is exactly the
G4d-i span-induction shape (`acolumn_mem_hingeRowBlock_of_span_rigidityRows` at
`Fv := ofNormals (G.removeVertex v) …`, whose `hdeg2` IS `hcla` restricted off `v`), and the
row-space correspondence `rigidityRows_ofNormals_relabel` (G4c-ii) transports the `v`-split
redundancy data onto the `a`-split rows. **(4)** A0/A1/B/A2 run verbatim at the `(a, c)` roles.
**Missing micro-leaves beyond M₁'s:** none new in kind — the M₃-specific work is the (1)–(3)
wiring; the GAP-6 input is the *same* carried inequality (same `r̂`, same redundancy data).
Verdict: **buildable after M₁ + the G4c/G4d wiring, modulo GAP 6**.

**(f) The corrected build order (supersedes §1.49(6) item 5's G4e clause for the discharge; each
item one commit unless noted):**

1. **W1 — the discriminator restate** ((a); RigidityMatrix.lean, both lemmas in place, proof
   reuse). Buildable now; first leaf.
2. **W2 — the `h618` micro-leaf** `finrank_span_rigidityRows_of_rigidOn` ((b);
   GenericityDevice.lean extraction + the two inline-`hfin` call sites optionally refactored).
3. **W3 — leaf B** (the one-variable rank transfer; graph-free).
4. **W4 — leaf A0** (the restriction-bottom augment; abstract, graph-free).
5. **W5 — the redundancy-data packaging** at the unpacked IH framework: `ab_lam` + W2 + the (b)
   `k''`-reduction, taking the **GAP-6 inequality as an explicit hypothesis** (per (b)(ii),
   pending adjudication). Output: `r`/`lam`/`i*`/`r̂ ≠ 0`/`hingeRow a b r̂ = wGv ∈ span(Gv-rows)`.
6. **W6 — A1 (M₁ `t = 0` certification at `F₀`)**, then **W7 — A2 (M₁ closer)**.
7. **W8 — M₂** (role-swap instantiation), **W9 — M₃** ((e) wiring), **W10 — the G4e dispatch +
   discharge assembly**: unpack `hsplitGP`, derive `hgab`/triple-LI, run the discriminator glue,
   `match u with 0 ↦ M₁ | 1 ↦ M₂ | 2 ↦ M₃`, ending at a lemma matching `case_III_hsplit_producer`'s
   `hcand` parameter shape exactly (plus the producer-level extras of (b) and the carried GAP-6
   hypothesis, all available at the Leaf-4 wiring site).
8. **Leaf 4 + Leaf 5** as in §1.49(6), with the GAP-6 hypothesis riding until its adjudicated
   discharge (option (i) restructure or a successor sub-phase).

**GAP 6 adjudicated (user, 2026-06-10): (ii) carry-and-defer** — see the (b) verdict above.

### 1.51 The W6-concrete decomposition — the single "W6-concrete/W7 M₁" slot of §1.50(f) is replaced by seven exact-signature leaves W6a–W6f + W7 (one commit each); PLUS one refinement of §1.50(c)'s sketch: the certified `t = 0` mixed family is NOT itself the transfer family `g` (its candidate row and transported `(vb)ⱼ`-rows are not sheared-candidate rows at `t ≠ 0`) — the route is **certify-then-rebase**: certify the KT-(6.29) count at `F₀`, convert it to a rank lower bound, re-extract a literal `F₀.panelRow` family, and transfer THAT (2026-06-11)

> **Docs-only design pass (the §1.50(c)/(f) build-out).** Lean re-read this pass (declarations,
> current line numbers): RigidityMatrix.lean — `linearIndependent_sum_restriction_block` (:1339,
> W4), `linearIndependent_sum_augment_candidateRow[_restriction]` (:1521/:1598, W6-core),
> `linearIndependent_sumElim_candidateRow_iff` (:1686), `hingeRow_comp_columnOp_{apply,vanish_off,
> comp_single}` (:1166/:1179/:1703), `hingeRow_comp_single_{tail,off}` (:1718/:1734), `columnOp` +
> `columnOp_apply_single`/`comp_columnOp_comp_single` (:1094–:1156), `mem_hingeRowBlock_iff`
> (:1664), `exists_complementIso_ne_zero_of_homogeneousIncidence` (:2155), `candidateRow_ac_eq_neg`
> (:1959); CaseI.lean — W5 `exists_redundant_panelRow_ab_lam[_of_rigidOn]` (:3207/:3276),
> `exists_candidate_row_eq612` (:3459), `case_III_old_new_blocks[_of_line]` (:3528/:3704),
> `case_III_full_family_of_line` (:3885), `candidateCompletion_{index_injective,panelRow_packaging}`
> (:3956/:4013), `case_III_realization_of_line` (:4076), C1/C2 (:2257/:2294),
> `exists_good_realization_const` (:2214), GAP-2 `hasGenericFullRankRealization_of_rigidOn_ofNormals`
> (:1971, incl. the §38-avoidance `hrow_mem` idiom :2011), the producer + `hcand` site (:4341),
> `hasGenericFullRankRealization_of_splitOff_relabel` (:4690, the `hQeq` unpack idiom);
> Pinning.lean — `panelRow` (:46), `span_panelRow_eq_rigidityRows` (:64),
> `span_panelRow_edge_eq` (:283), `finrank_span_panelRow_edge` (:305),
> `span_rigidityRows_eq_sup_span_panelRow_edge` (:343),
> `exists_independent_panelRow_subfamily_of_edge` (:442),
> `linearIndependent_panelRow_comp_single_of_edge` (:503), `span_panelRow_comp_single_of_edge`
> (:547); GenericityDevice.lean — W2 (:466), `exists_independent_panelRow_subfamily_of_rigidOn
> [_linking]` (:561/:627); PanelLayer.lean — `panelSupportExtensor_{add_smul_right,add_smul_left,
> swap,ne_zero_iff,eq_complementIso_extensor}` (:238/:251/:225/:212/:277), `annihRow` +
> `span_annihRow_eq_dualAnnihilator` (:800/:833), `exists_shear_linearIndependent_pair` (:363);
> Rank.lean (Mathlib mirror) — W3 `LinearIndependent.exists_notMem_of_polynomial_repr` (:644);
> PanelHinge.lean — `ofNormals` (:253), the two motives (:979/:1033). KT re-read this pass:
> pp. 681–686 (the sketch; eqs. (6.18)–(6.30); Claim 6.11; footnote 6) —
> `.refs/katoh-tanigawa-2011-molecular-conjecture.pdf`, printed p. N = pdf p. N − 646; the
> Lemma 5.2 mechanism (pp. 668–669) rides on §1.50's verified read (model-experiment row 20).
> No `.lean`/`.tex` edits this pass.

**(a) The refinement of §1.50(c) — certify-then-rebase (machine-checked against the Lean + KT
pp. 684–686).** §1.50(c) sketched the certifying family `g` as "`g 0` is the `F₀`-certified
KT-(6.29) family". That is not literally transferable: the certified (6.29) family contains the
candidate row `hingeRow v a ρ` (with `ρ(C(L)) ≠ 0`, so for `t ≠ 0` it is *not* in the sheared
candidate's row span — the same obstruction §1.50(c) diagnosed for the `_of_line` OLD-contract)
and the transported `(vb)ⱼ`-rows `hingeRow v b ρⱼ` (`ρⱼ ∈ (span C(e₀))^⊥`, not rows of the sheared
candidate whose `e_b`-support is `C(e₀) + t·(n' ∧ n_b) ≠ C(e₀)`). The corrected route inserts one
rank-rebase step, exactly KT's own reading of (6.29) ("if the top-left 6×6 block is full rank,
then rank R(G,p₁) = 6(|V|−1)", p. 684 — a statement about the *rank* of `R(G,p₁)`, not about a
distinguished row family):

1. **Certify** the mixed (6.29) family — `(D−1)` `e_a`-rows ⊕ the candidate `hingeRow v a ρ` ⊕
   the chosen `D(m_v−1)` bottom rows — linearly independent at `F₀` (W6c + W6d below).
2. **Rebase**: every member lies in `span ℝ F₀.rigidityRows` (`e_a`-rows genuine; the candidate
   via the eq.-(6.27) collapse `hingeRow v a ρ = hingeRow v b ρ − hingeRow a b ρ`, with
   `hingeRow v b ρ` a genuine `F₀`-row — `ρ ∈ (span C(e₀))^⊥ = F₀`'s `e_b`-block — and
   `hingeRow a b ρ = r̂ ∈ span(G_v\text{-rows}) ⊆ span F₀`-rows; the bottom per-tag), so
   `D(|V(G)|−1) ≤ finrank (span ℝ F₀.rigidityRows)`, and a **literal `F₀.panelRow` family** of
   that size is re-extracted (W6e). Each slot of the re-extracted family is an
   `annihRow`-of-the-edge-extensor row, which IS polynomial in the shear parameter.
3. **Transfer** the re-extracted family along the one-parameter `t`-family of hinge-level
   frameworks `F(t)` (`F(0) = F₀`; only the `e_b`-slot moves, linearly) via W3 (W6f), then read
   every `F(t^*)`-slot as a (scaled) genuine row of `ofNormals G ends (q₀ t^*)` and close through
   the span-containment core + GAP-2 (W7).

Everything else in §1.50(c) stands: `F₀` hinge-primary, memberships at `t = 0` by construction,
the witness gate `r̂(C(L)) ≠ 0` consumed at `t = 0` only, the obsolete sheared-support step.

**(b) The `t`-family `F(t)` and the infra bricks — leaf W6a (CaseI.lean def + PanelLayer.lean /
RigidityMatrix.lean bricks; one commit; no §38).** KT's `p₁` (eq. (6.12)) at shear `t`, hinge-level
and role-parametric (M₁: `e_c := e_a, e_r := e_b, n_u := n_a, n_r := n_b`; M₂ swaps `a ↔ b`; M₃
passes the relabeled seed `qρ` — §1.50(d)/(e)):

```lean
-- CaseI.lean. `e_c` = the candidate hinge (the free line `L = n_u ∧ n'`), `e_r` = the reproduced
-- hinge (`= n_u ∧ n_r` at `t = 0`, KT's `p₁(vb) = q(ab)`); all other edges keep the seed extensor.
noncomputable def PanelHingeFramework.caseIIICandidate [DecidableEq β]
    (G : Graph α β) (ends : β → α × α) (q : α × Fin (k + 2) → ℝ)
    (e_c e_r : β) (n_u n' n_r : Fin (k + 2) → ℝ) (t : ℝ) :
    BodyHingeFramework k α β where
  graph := G
  supportExtensor := Function.update (Function.update
      ((PanelHingeFramework.ofNormals G ends q).toBodyHinge.supportExtensor)
      e_c (panelSupportExtensor n_u n'))
    e_r (panelSupportExtensor (n_u + t • n') n_r)
```

with evaluation/affinity lemmas (statement shapes; `caseIIICandidate_graph … = G := rfl`):

```lean
theorem caseIIICandidate_supportExtensor_candidate (hcr : e_c ≠ e_r) :
    (caseIIICandidate G ends q e_c e_r n_u n' n_r t).supportExtensor e_c
      = panelSupportExtensor n_u n'
theorem caseIIICandidate_supportExtensor_reproduced :
    (caseIIICandidate …).supportExtensor e_r = panelSupportExtensor (n_u + t • n') n_r
theorem caseIIICandidate_supportExtensor_of_ne (h1 : e ≠ e_c) (h2 : e ≠ e_r) :
    (caseIIICandidate …).supportExtensor e
      = (PanelHingeFramework.ofNormals G ends q).toBodyHinge.supportExtensor e
-- the W6f polynomiality input: only the `e_r`-slot moves, linearly in `t`
theorem caseIIICandidate_panelRow_eq_add_smul (hcr : e_c ≠ e_r) (t : ℝ) (p : β × _ × _) :
    (caseIIICandidate G ends q e_c e_r n_u n' n_r t).panelRow ends p
      = (caseIIICandidate G ends q e_c e_r n_u n' n_r 0).panelRow ends p
        + t • (if p.1 = e_r then BodyHingeFramework.hingeRow (ends e_r).1 (ends e_r).2
            (annihRow (panelSupportExtensor n' n_r) p.2.1 p.2.2) else 0)
```

At `t = 0`, `e_r ↦ panelSupportExtensor n_u n_r` — for M₁ that is `C(e₀)` exactly (KT's
`p₁(vb) = q(ab)` reproduction; verified against the p. 686 eq.-(6.28) computation
"`R(G, p₁; (vb)ⱼ, v) = rⱼ(p₁(vb)) = rⱼ(q(ab))` … by `p₁(vb) = q(ab)`"); for M₂ it is
`panelSupportExtensor n_b n_a = −C(e₀)` (`panelSupportExtensor_swap`), harmless — every
consumer reads the extensor only through `(span {C})^⊥`-membership or `≠ 0`, both sign-blind.
The supporting bricks, same commit:

```lean
-- PanelLayer.lean (first-slot linearity; the `map_update_add/smul` idiom of
-- `panelSupportExtensor_add_smul_left`, which becomes a corollary):
theorem panelSupportExtensor_add_left  : panelSupportExtensor (n₁ + n₂) n₃
  = panelSupportExtensor n₁ n₃ + panelSupportExtensor (k := k) n₂ n₃
theorem panelSupportExtensor_smul_left : panelSupportExtensor (c • n₁) n₂
  = c • panelSupportExtensor (k := k) n₁ n₂
-- PanelLayer.lean (annihRow is linear in its extensor — load-bearing per §1.50's recon note):
theorem annihRow_add  : annihRow (C + C') t₁ t₂ = annihRow C t₁ t₂ + annihRow C' t₁ t₂
theorem annihRow_smul : annihRow (c • C) t₁ t₂ = c • annihRow C t₁ t₂
-- PanelLayer.lean (the GAP-3 bad set as a *set* — `exists_shear_linearIndependent_pair`'s inline
-- `hbad_unique`, extracted so W7 can intersect it with W3's finite bad set; the landed existence
-- lemma is refactored to consume it):
theorem setOf_not_shear_linearIndependent_subsingleton (n_a n' n_b : Fin (k + 2) → ℝ)
    (hgab : LinearIndependent ℝ ![n_a, n_b]) :
    {t : ℝ | ¬ LinearIndependent ℝ ![n_a + t • n', n_b]}.Subsingleton
-- RigidityMatrix.lean (the two restriction-transport bricks; `P_v := id − single v ∘ proj v`,
-- W4's off-`v` projection). Brick 1 is the (6.26)–(6.28) membership-by-construction in
-- functional form: the operated, restricted `(vb)ⱼ`-transport IS the `(ab)ⱼ`-row —
-- `(Φ (P_v S)) v = S a`, `(Φ (P_v S)) b = S b`, so the composite reads `ρ (S a − S b)`:
theorem BodyHingeFramework.hingeRow_comp_columnOp_comp_offProj [DecidableEq α] {v a b : α}
    (hva : v ≠ a) (hvb : v ≠ b) (ρ : Module.Dual ℝ (ScrewSpace k)) :
    ((hingeRow (k := k) (α := α) v b ρ).comp (columnOp (k := k) hva).toLinearMap).comp
        ((LinearMap.id : (α → ScrewSpace k) →ₗ[ℝ] (α → ScrewSpace k))
          - (LinearMap.single ℝ (fun _ : α => ScrewSpace k) v).comp (LinearMap.proj v))
      = hingeRow (k := k) (α := α) a b ρ
-- Brick 2: a row reading nothing on `v`'s column is untouched by `Φ` and `P_v`
-- (`Φ S = S + single v (S a)`, `P_v S = S − single v (S v)`, both killed by `hg`):
theorem BodyHingeFramework.comp_columnOp_comp_offProj_of_single_eq_zero [DecidableEq α]
    {v a : α} (hva : v ≠ a) {g : Module.Dual ℝ (α → ScrewSpace k)}
    (hg : g.comp (LinearMap.single ℝ (fun _ : α => ScrewSpace k) v) = 0) :
    (g.comp (columnOp (k := k) hva).toLinearMap).comp
        ((LinearMap.id : (α → ScrewSpace k) →ₗ[ℝ] (α → ScrewSpace k))
          - (LinearMap.single ℝ (fun _ : α => ScrewSpace k) v).comp (LinearMap.proj v)) = g
```

Consumes: landed `panelSupportExtensor`/`annihRow`/`columnOp` API. Consumed by: W6c–W6f, W7
(every later leaf names `caseIIICandidate`; consumed-by-spec, not speculative). No `\lean` pin
(internal infra, the W4/W5 pattern).

**(c) The candidate/bottom data packaging — leaf W6b (CaseI.lean; one commit; no new §38).** The
M₁/M₂ arms need, from ONE invocation of W5's redundancy data (KT p. 686: "the same `λ_{(ab)j}` …
and the index `i^*` are used in (6.29) and (6.30)"), two things tied to the same `i^*`: the
candidate functional `ρ` (KT's `r̂ = Σ_j λ_{(ab)j} r_j(q(ab))` read as a `ScrewSpace`-functional
through `r̂ = hingeRow a b ρ`) and the chosen `D(m−1)` bottom rows of `R(G_v^{ab} ∖ (ab)i^*, q)`
(KT eq. (6.23): that matrix has full rank `D(m−1)`, p. 685). Signature (hypotheses = W5's
verbatim; stated at `(ends e₀).1/.2` so no `hends_e0` is consumed — the W10 wiring rewrites):

```lean
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
    -- GAP 6 (adjudicated carry, §1.50(b)): enters HERE (via W5, whose sole caller this becomes)
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
          w j = BodyHingeFramework.hingeRow (ends e₀).1 (ends e₀).2 ρ')
```

Proof route: invoke W5 (`exists_redundant_panelRow_ab_lam_of_rigidOn`) → `r̂ := ∑ j, lam j • r j`;
`ρ` from `r̂ ∈ span(range r) = e₀-block-span = map (screwDiff …).dualMap (hingeRowBlock e₀)`
(`hrspan` + `span_panelRow_edge_eq` + `hingeRow_eq_dualMap`; annihilation via
`mem_hingeRowBlock_iff`; `ρ ≠ 0` since `r̂ ≠ 0` and `hingeRow` is linear in `ρ`). Bottom rows:
`lam i^* = 1` makes `r i^* = r̂ − ∑_{j ≠ i^*} lam j • r j ∈ span(Fv.rigidityRows) ⊔
span(r '' {j ≠ i^*})`, so `span(Fv.rigidityRows ∪ range (r ∘ Subtype.val : {j // j ≠ i^*} → _))
= span(Fab-rows)` (via `span_rigidityRows_eq_sup_span_panelRow_edge` + `hrspan`), of finrank
`D(m−1)` (W2 re-derivation, the `hgraph : Fab.graph = Gab := rfl` idiom of W5);
`Submodule.exists_fun_fin_finrank_span_eq` extracts `w` with per-member tags (an `r j'`-tagged
member yields its `ρ'` through the same block destructuring). Consumes: W5, W2,
`span_panelRow_edge_eq`, `span_rigidityRows_eq_sup_span_panelRow_edge`. Consumed by: W10 (which
feeds the outputs to the glue — `ρ ≠ 0` is the discriminator's `hr` — and to W7/W8 as data).
**GAP-6 path:** `h622lb` enters the Lean at W5, is carried by W6b (W5's sole caller), and next
appears on W10's signature — W6c–W6f and W7 below take W6b's *outputs* as hypotheses and are
GAP-6-clean. No `\lean` pin.

**(d) The restriction-form full family — leaf W6c (CaseI.lean; one commit; no §38; independently
buildable NOW).** The restriction-bottom sibling of `case_III_full_family_of_line` — same NEW-block
construction (the `D−1` `e_a`-panel-rows + the candidate, via the row-space criterion), but the
bottom block enters with W4's restriction-independence contract and the assembly is W6-core
instead of the v-vanishing selector. Stated over abstract `F` (serves M₁/M₂/M₃):

```lean
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
          ro)
```

Proof route: mirror `case_III_full_family_of_line`'s body — `exists_independent_panelRow_
subfamily_of_edge` + `linearIndependent_panelRow_comp_single_of_edge` +
`span_panelRow_comp_single_of_edge` + the `comp_columnOp_comp_single` bridge give the operated
pinned NEW block and its span; `hnewpinaug` closes by `rw [hingeRow_comp_columnOp_comp_single]` +
`(linearIndependent_sumElim_candidateRow_iff F e_a … r).2 hr` (verbatim the selector's :1913
two-liner); `hrnvanish` for the `sn`-rows is `hends_ea`-rewrite + `hingeRow_comp_columnOp_vanish_
off`; finish with W6-core `linearIndependent_sum_augment_candidateRow_restriction` in place of the
selector. Consumes: W6-core, W4-era bricks (all landed — no W6a/W6b dependency). Consumed by:
W6d. No `\lean` pin.

**(e) The `t = 0` rank certification — leaf W6d (CaseI.lean; one commit; §38 exposure: moderate,
mitigated).** The (6.29) count at `F₀ := caseIIICandidate G ends q e_a e_b n_a n' n_b 0`,
concluded as the rank lower bound (per (a) step 2 — the consumable form). The bottom family rides
abstractly-indexed (`ιb` + `Nat.card`), so W6b's `Fin`-indexed output feeds it without a cast and
the leaf builds independently of W6b:

```lean
theorem PanelHingeFramework.case_III_rank_certification
    [DecidableEq α] [DecidableEq β] [Finite α]
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
            (fun i => q (a, i)) n' (fun i => q (b, i)) 0).rigidityRows)
```

Proof route: (i) **transport the bottom** — define `w̃ j := w j` on the `Fv`-tag (a literal
`Fv`-generator `hingeRow u w' r'` with `u, w' ≠ v` by `hvVc`; brick 2 applies via
`hingeRow_comp_single_off`, so its `Φ/P_v`-composite is `w j` itself) and
`w̃ j := hingeRow v b ρ'` on the `ρ'`-tag (brick 1 makes the composite `hingeRow a b ρ' = w j`);
the composite family is `w`, so `hbotrestrict` holds by `hw`. (ii) **A1** — feed W6c at `F := F₀`,
`ro := w̃`, `r := ρ` (`hane` via `caseIIICandidate_supportExtensor_candidate heab` +
`panelSupportExtensor_ne_zero_iff.mpr hLn`; the gate is `hρgate` through the same simp). (iii)
**memberships** — every member of the certified family is in `span ℝ F₀.rigidityRows`: `sn`-rows
by `panelRow_mem_rigidityRows_of_link hends_ea hG_ea`; the candidate by the collapse
`hingeRow v a ρ = hingeRow v b ρ − hingeRow a b ρ` (`hingeRow_sub_hingeRow_eq`) with
`hingeRow v b ρ ∈ F₀.rigidityRows` (witness `⟨e_b, v, b, hG_eb, ρ, mem_hingeRowBlock_iff.mpr ∘
(caseIIICandidate_supportExtensor_reproduced ▸ hρe₀-at-t=0), rfl⟩` — at `t = 0` the `e_b`-extensor
is `panelSupportExtensor n_a n_b`, the `hρe₀` shape exactly) and `hingeRow a b ρ ∈
span(Fv-rows) ⊆ span(F₀-rows)` (each `Fv`-generator is an `F₀`-row: `hleG`-link + equal extensor
off `{e_a, e_b}` — a `Gv`-edge is neither, derivable from `hvVc` + edge-uniqueness against
`hG_ea`/`hG_eb`); the bottom `w̃`-rows per-tag the same way. (iv) **count** — the family is
`(sn ⊕ Unit) ⊕ ιb` of card `((D−1)+1) + D(m_v−1) = D·m_v = D(|V(G)|−1)` (`hwcard`/`hVcard`/
`hVone`, omega); `finrank_span_eq_card` + `Submodule.finrank_mono` convert LI-in-span to the
bound. **§38 note:** `F₀`'s extensors are reached ONLY through the three W6a simp lemmas (the
`update`-form never meets `whnf`); memberships are built with explicit link witnesses (the
`hrow_mem` idiom, CaseI.lean:2011). Consumes: W6a, W6c, brick 1/2, landed collapse +
membership bricks. Consumed by: W7. No `\lean` pin.

**(f) The rank-bound panelRow re-extraction — leaf W6e (GenericityDevice.lean; one commit; no
§38; independently buildable NOW).** The generalization of
`exists_independent_panelRow_subfamily_of_rigidOn_linking` that replaces the rigidity input
(`hnev`/`hrig`, used there only to compute `finrank(span rigidityRows)` via W2) by the rank bound
itself — the form step (a)2→3 consumes at the *not-yet-known-rigid* `F₀`:

```lean
theorem BodyHingeFramework.exists_independent_panelRow_subfamily_of_le_finrank
    [Finite α] [Finite β] (F : BodyHingeFramework k α β) {ends : β → α × α}
    (hends : ∀ e u v, F.graph.IsLink e u v → F.graph.IsLink e (ends e).1 (ends e).2)
    (hne : ∀ e, F.graph.IsLink e (ends e).1 (ends e).2 → F.supportExtensor e ≠ 0)
    {N : ℕ} (hN : N ≤ Module.finrank ℝ (Submodule.span ℝ F.rigidityRows)) :
    ∃ s : Set (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k),
      (∀ i ∈ s, F.graph.IsLink (i : β × _ × _).1 (ends (i : β × _ × _).1).1
        (ends (i : β × _ × _).1).2) ∧
      Nat.card s = N ∧
      LinearIndependent ℝ (fun i : s => F.panelRow ends (i : β × _ × _))
```

Proof route: the `_of_rigidOn_linking` skeleton verbatim (`span_panelRow_linking_eq_rigidityRows`
→ `Submodule.exists_fun_fin_finrank_span_eq` over the linking-index subtype → `choose`/re-index),
with the extracted `Fin (finrank …)`-family cut to its first `N` members through `Fin.castLE hN`
(sub-family of an LI family). Refactor `_of_rigidOn_linking` in the same commit to be the 3-line
corollary via W2 (its `hfin` block is exactly W2 + the span identity) — the same
extract-and-refactor move W2 itself made. Consumed by: W7 (and reusable beyond — the lemma is the
honest "rank ⟹ that many literal panel rows" converter the device family lacked). No `\lean` pin.

**(g) The one-variable transfer at the `t`-family — leaf W6f (CaseI.lean; one commit; no §38).**
The W3 feed specialized to `caseIIICandidate` (per (a) step 3):

```lean
theorem PanelHingeFramework.caseIIICandidate_exists_good_shear
    [DecidableEq β] [Finite α]
    (G : Graph α β) (ends : β → α × α) (q : α × Fin (k + 2) → ℝ)
    {e_c e_r : β} (hcr : e_c ≠ e_r) (n_u n' n_r : Fin (k + 2) → ℝ)
    {ι : Type*} [Finite ι]
    (idx : ι → β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k)
    (h0 : LinearIndependent ℝ (fun i => (PanelHingeFramework.caseIIICandidate G ends q
      e_c e_r n_u n' n_r 0).panelRow ends (idx i)))
    (bad : Finset ℝ) :
    ∃ t : ℝ, t ∉ bad ∧ t ≠ 0 ∧ LinearIndependent ℝ (fun i =>
      (PanelHingeFramework.caseIIICandidate G ends q e_c e_r n_u n' n_r t).panelRow ends (idx i))
```

Proof route: `g t i := (caseIIICandidate … t).panelRow ends (idx i)`;
`caseIIICandidate_panelRow_eq_add_smul` (W6a) gives `g t i = A i + t • B i` (`A` the `t = 0` rows,
`B` the `e_r`-correction, `0` off `e_r`); take `b := Module.finBasis ℝ (Module.Dual ℝ (α →
ScrewSpace k))` and `P i j := Polynomial.C (b.repr (A i) j) + Polynomial.X * Polynomial.C
(b.repr (B i) j)` (degree ≤ 1; `hg` by `map_add`/`map_smul` of `b.repr`); apply W3
`LinearIndependent.exists_notMem_of_polynomial_repr`. This is KT Lemma 5.2's "each minor of
`R(G, p_t)` is continuous in `t`" (pp. 668–669) in its one-variable polynomial form. Consumes:
W6a, W3. Consumed by: W7. No `\lean` pin.

**(h) The arm closer — leaf W7 (CaseI.lean; one commit; THE §38-exposed leaf, mitigations
named).** The role-parametric arm: from the unpacked-split context + W6b's data, the generic
motive. Supersedes the §1.50(f) "W7 — A2 (M₁ closer)" slot; W8 (M₂) becomes a pure
instantiation of this lemma (see (i)):

```lean
theorem PanelHingeFramework.case_III_arm_realization
    [DecidableEq α] [DecidableEq β] [Finite α] [Finite β]
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
        w j = BodyHingeFramework.hingeRow a b ρ') :
    PanelHingeFramework.HasGenericFullRankRealization k G
```

Proof route: (i) W6d → the rank bound at `F₀`; (ii) W6e at `F₀` (`hends` at `F₀.graph = G`
derived from `hsplitG`/`hends_Gv`/`hleG` + the two recorded links; `hne` on linking edges:
`e_a ↦ C(L) ≠ 0` by `hLn`, `e_b ↦ panelSupportExtensor n_a n_b ≠ 0` by `hgab`, `Gv`-edges by
`hne_Gv` + extensor agreement) → a linking index set `s`, `Nat.card s = D(|V(G)|−1)`, literal
`F₀.panelRow`-family LI; (iii) W6f with `bad := ((setOf_not_shear_linearIndependent_subsingleton
… hgab).finite.toFinset)` → `t^* ∉ bad`, `t^* ≠ 0`, the `F(t^*)`-family LI, and (by `t^* ∉ bad`,
contraposition) `LinearIndependent ℝ ![n_a + t^* • n', n_b]`; (iv) **membership at `t^*`** —
define `q₀ : α × Fin (k+2) → ℝ := fun p => if p.1 = v then (n_a + t^* • n') p.2 else q p` (the
`hq₀v/hq₀b/hq₀a` funext-`if_neg` pattern of `case_III_old_new_blocks`); each `F(t^*)`-slot is in
`span ℝ (ofNormals G ends q₀).toBodyHinge.rigidityRows`: the `e_r = e_b`-slot and the `Gv`-slots
have extensors *equal* to the sheared candidate's (the `e_b`-normals are `(n_a + t^*n', n_b)`
exactly; `Gv`-endpoints avoid `v`), so they are genuine rows (`panelRow_mem_rigidityRows_of_link`
at `hG_eb` / the `hleG`-links); the `e_c = e_a`-slot is `(−1/t^*) •` the genuine `e_a`-row
(`panelSupportExtensor_add_smul_left` makes the sheared `e_a`-extensor `(−t^*) • C(L)`;
`annihRow_smul` (W6a) scales the row; `t^* ≠ 0` inverts); (v) **close** —
`isInfinitesimallyRigidOn_vertexSet_of_span_le_rigidityRows` (count = `Nat.card s`) gives rigidOn
`V(G)` at `ofNormals G ends q₀`, and GAP-2 `hasGenericFullRankRealization_of_rigidOn_ofNormals`
(its `hends` = the derived G-level one; its `hne` = the (ii) list at `q₀`) concludes. **§38
mitigations:** the only concrete carrier is `ofNormals G ends q₀` in (iv)–(v); all memberships
are built with explicit link witnesses (the `hrow_mem` idiom, CaseI.lean:2011), all extensor
evaluations go through `toBodyHinge_supportExtensor`/`ofNormals_normal` rewrites plus the W6a
simp lemmas, and the `q₀`-overrides through the funext-`if_neg` pattern — never `whnf` on the
carrier. Consumes: W6d, W6e, W6f, W6a's subsingleton, GAP-2, the span-containment core. Consumed
by: W10 (M₁ at the listed roles, M₂ per (i) below, M₃ after the W9 wiring). No `\lean` pin.

**(i) What supersedes what; M₂/M₃/W10 under the new cut.** The §1.50(f) build-order items
6 ("W6 — A1, then W7 — A2") are **superseded** by W6a–W6f + W7 above; §1.50(c)'s leaf names map
A1 ↦ W6c + W6d, A2 ↦ W6e + W6f + W7 (with the (a) certify-then-rebase correction). Items W8–W10
keep their names and slots, refined:

* **W8 (M₂)** is an *instantiation commit* of W7 at the swapped roles `(a, b, e_a, e_b, n') :=
  (b, a, e_b, e_a, n'')`, feeding `ρ' := −ρ`: the swapped-role candidate functional is `−ρ`
  because `r̂ = hingeRow a b ρ = hingeRow b a (−ρ)` (`hingeRow_swap`) — a Lean-orientation
  artifact, not a KT discrepancy (KT p. 681: "`r'` is indeed equal to `r`"; the row content is
  identical). Its `hρe₀`/`hwmem` shapes convert by `panelSupportExtensor_swap` + `map_neg`; the
  gate at the `u = 1` witness is `ρ(panelSupportExtensor n_b n'') ≠ 0 → (−ρ)(…) ≠ 0`. If the
  conversion is genuinely small it may be inlined into W10's `u = 1` branch; budget it as its own
  commit.
* **W9 (M₃)** stays as scoped in §1.50(e) (the G4c/G4d wiring + `candidateRow_ac_eq_neg`),
  now targeting W7 at the *relabeled* `a`-split data: the `caseIIICandidate` def takes the
  relabeled seed `qρ` as its `q`-argument, and W7's `(v, a, b, e_a, e_b, n')`-slots are
  instantiated at `(a, c, v, e_c, e_a, n''')` — re-inserted body `a`, candidate hinge `e_c = ac`
  on the line `L'' ⊂ Π(c)` (the `u = 2` witness), reproduced hinge `e_a = av` at the relabeled
  split's `vc`-hinge (§1.50(e)'s `p₃(av) = qρ(vc)`), `Gv`-slot the relabeled split minus its
  short-circuit edge. The candidate functional arrives as the *same* `ρ` through
  `candidateRow_ac_eq_neg` + the `rigidityRows_ofNormals_relabel` row-space transport; pin the
  residual sign/wiring shapes at the W9 design moment, after W7 lands.
* **W10 (dispatch + discharge)** unchanged in role: unpack `hsplitGP` (the `hQeq` idiom,
  CaseI.lean:4704), override the selector at the two re-inserted hinges (`ends' := Function.update
  (Function.update Q.ends e_a (v, a)) e_b (v, b)` — the IH selector is junk off `E(Gab)`, and
  `e_a, e_b ∉ E(Gab)`; `e₀ ∈ E(Gab)` keeps its recorded pair, *possibly in either order* — the
  recordsLinks conjunct pins it only up to swap, so W10 case-splits and feeds the arms with
  `(a, b)` named in recorded order), derive `hgab`/triple-LI from GP, `hne_Gv` from GP +
  `supportExtensor_ne_zero_of_isGeneralPosition`, invoke **W6b** (GAP-6 `h622lb` on W10's
  signature), run the discriminator glue at `hr := ρ ≠ 0`, bridge the gate to the arm shape via
  `panelSupportExtensor_eq_complementIso_extensor`, and `match u with | 0 => W7 | 1 => W8 |
  2 => W9`, ending at `case_III_hsplit_producer`'s `hcand` parameter shape.

**(j) The corrected build order (replaces §1.50(f) item 6; each item one commit).**
~~W1–W5, W6-core~~ (landed) → **W6a** (infra bricks + the `t`-family def) → **W6c** ∥ **W6e**
(both independently buildable now — only landed inputs; order between them free) → **W6b** (the
packaging; first GAP-6 carry above W5) → **W6f** (the transfer feed) → **W6d** (the `t = 0`
certification) → **W7** (the arm closer) → **W8** (M₂ instantiation) → **W9** (M₃ wiring,
§1.50(e)) → **W10** (dispatch + discharge assembly, matching `hcand`) → Leaf 4 → Leaf 5, phase
close **green-modulo-GAP-6**. Dependency edges (anything not listed is independent):
W6d ← {W6a, W6c}; W6f ← W6a; W7 ← {W6d, W6e, W6f}; W8/W9/W10 as in (i). All seven new leaves are
statement-complete above — a build agent picks the leftmost unlanded leaf and lands it whole (no
`sorry`; the only carried hypothesis anywhere is GAP-6's `h622lb`, and only on W6b/W10+). The
pinned signatures fix the mathematical content (binders, hypotheses, conclusion); instance-set
adjustments (`[Finite β]`, `[DecidableEq …]`) demanded by elaboration are at the builder's
discretion and are not design deviations.

### 1.52 The W9 design moment — verdict: W9 IS a W7-instantiation at `Gv := G − a` with the relabeled seed `qρ` (the 365740b "not-a-W7-instantiation" finding is true of a configuration the design never proposed — the a-split graph is NOT the `Gv`-slot and never enters the live chain); the M₃ candidate/bottom data transports POINTWISE from the ONE v-split W6b invocation (KT eqs. (6.35)–(6.41): `R(G,p₃)`'s bottom block IS the v-split matrix `R(G_v^{ab} ∖ (ab)i^*, q)` read inside it through the vertex relabel — no a-split rank, no second redundancy, no second GAP-6); two new transport leaves W9a/W9b + the closer W9c; the relabel-SPAN bridge and the G4c-ii/G4d-ii suite drop off the live route (2026-06-11)

> **Docs-only design pass (the §1.50(e)/§1.51(i) W9 build-out).** Lean read this pass
> (declarations, current line numbers): CaseI.lean — W7 `case_III_arm_realization` (:4549, full
> body incl. the step-(iii)–(v) membership/close mechanics), W8 `case_III_arm_realization_M2`
> (:4794, the instantiation pattern), W6b `exists_candidateRow_bottomRows_of_rigidOn` (:3357, full
> body — the `hext : ∀ e, Fab.supportExtensor e = Fv.supportExtensor e := fun _ => rfl` idiom),
> `exists_redundant_panelRow_ab_decomposition_acolumn_zero` (:3489), G4c-ii `ofNormals_relabel` /
> `rigidityRows_ofNormals_relabel` / `hasGenericFullRankRealization_of_splitOff_relabel` (:5375/
> :5513/:5601), the W9 bridge `mem_span_rigidityRows_ofNormals_relabel` (:5652), G4d-i/ii
> (:5691/:5759), the triple-LI bridge (:5799); RigidityMatrix.lean — `hingeRow_funLeft_dualMap`
> (:851), `hingeRow_swap` (:837), `hingeRow_sub_hingeRow_eq` (:867), `rigidityRows` (:905 — rows
> quantify over LINKS only; `ends` is read only at linked edges), `hingeRowBlock` (:739),
> `candidateRow_ac_eq_neg` (:2051), `case_III_claim612` (:2105); Operations.lean — `removeVertex`
> + `removeVertex_isLink`/`vertexSet_removeVertex`/`removeVertex_le_splitOff` (:536–:690),
> `splitOff`/`splitOff_isLink` (:579/:619). KT re-read: pp. 684–686 (Claim 6.11, eqs.
> (6.22)–(6.30) — "the same λ_{(ab)j} … and the index i^* are used in (6.29) and (6.30) since they
> are determined by (G_v^{ab}, q)"), **pp. 687–689 (eqs. (6.31)–(6.41) in full — the decisive M₃
> mechanics)**, p. 690 (eq. (6.42), Claim 6.12). No `.lean`/`.tex` edits this pass.

**(a) The adjudication — W7-instantiation at `Gv := G − a` WINS; the re-derivation route is
strictly dominated (signature-level).** The 365740b hand-off finding said: W7's `hleG` forces its
`Gv`-slot to be a subgraph of `G`, the M₃ rigidity certificate lives on the relabeled `a`-split
`G.splitOff a v c e₁` ∉ subgraphs of `G`, hence "W9 must re-derive W7's certify-then-rebase chain
with the relabeled framework as the rigidity source". The premise is true; the conclusion attacks
a configuration §1.51(i) never proposed — its `Gv`-slot is "**the relabeled split minus its
short-circuit edge**", i.e. edge-wise `G − a` (`G.removeVertex a`), which IS a subgraph of `G`.
The real question the finding pointed at is where the M₃ candidate/bottom data at the
`(G − a, qρ)`-shape comes from. KT answers it at eqs. (6.35)–(6.41) (pp. 687–689), re-read in
full this pass:

* **KT never realizes the a-split.** The isomorphism `ρ` (6.31) only *defines* `p₃` (the seed
  `qρ`) and identifies panels. The rank argument runs bodily against `R(G, p₃)`: the (6.36)
  column op adds `a`'s columns to `c`'s — *exactly* the landed `columnOp` of W6c/W6d at the role
  pair `(v\text{-slot}, a\text{-slot}) = (a, c)` — and (6.38)–(6.39) identify the resulting
  `E∖{ac}, V∖{a}`-submatrix with `R(G_v^{ab}, q)` via the row correspondence `(vb)_j ↔ (ab)_j`,
  `(va)_j ↔ (ac)_j`, `e_j ↔ e_j`. The bottom block of (6.41) is **`R(G_v^{ab} ∖ (ab)i^*, q)` —
  the same v-split matrix as M₁/M₂'s (6.29)/(6.30)**, same `λ`s, same `i^*`, rank by the same
  (6.23). There is no a-split rank certification anywhere, hence no eq.-(6.22)-analogue at
  `G − a`, hence **no second GAP-6**.
* **The Lean's `caseIIICandidate` at the §1.51(i) roles is literally KT's `p₃`.** Instantiating
  W7 at `(v, a, b, e_a, e_b, n') := (a, c, v, e_c, e_a, n''')`, `q := qρ` (inline:
  `fun p => q (Equiv.swap a v p.1, p.2)`), the `t = 0` framework has `e_c ↦ C(L'') = n_c ∧ n'''`,
  `e_a ↦ n_c ∧ n_a = ±C(q(ac))` (KT `p₃(va) = q(ac)`), `e_b ↦` the seed extensor at
  `(qρ(v,·), qρ(b,·)) = (n_a, n_b) = C(q(ab))` (KT `p₃(vb) = q(ab)`), all other edges the
  `q`-extensors — eq. (6.33) slot for slot. W7's internal shear `q₀ : a ↦ n_c + t•n'''` is the
  `Π(c)`-line shear, its W6d certification is the (6.41) count, its brick-1 transport at the
  roles (`hingeRow a v ρ' ∘ Φ ∘ P_a = hingeRow c v ρ'`) is exactly KT's (6.39) row
  correspondence read functional-wise.
* **The three §1.51(i) residual questions resolve as follows.** (1) *Short-circuit elimination:*
  there is no span-level `e₁`-elimination — the M₃ analogue of "the `λ/i^*` redundancy inside
  W6b" is a **pointwise generator transport**: each v-split datum maps under
  `(funLeft (Equiv.swap a v)).dualMap` and the image is classified by the degree-2-at-`a` fact
  (`hcla`): `(ab)`-block rows `hingeRow a b ρ' ↦ hingeRow v b ρ'` = genuine `e_b`-rows of
  `G − a`; `e_c`-rows `hingeRow a c r ↦ hingeRow v c r = hingeRow c v (−r)` = exactly W7's
  `hwmem` ρ'-TAG (the `(c,v)`-block tag, realized inside W7 as the `e_a = (av)`-row of `F₀` —
  KT's `(va)_j ↔ (ac)_j`); rows avoiding `a, v` are fixed and stay genuine rows. The candidate
  membership (`hρGv`-slot) needs one new span-induction leaf (W9a below) because W6b's
  *forgetful* span output can't be classified post hoc. (2) *`ends`-selector:* dissolved for W9 —
  `rigidityRows` (:905) reads `ends` only at linked edges, and the W9 transport leaves re-derive
  every membership generator-wise *at the target selector* `ends₃ := update³ ends₀` (pinned
  `(a,c)/(a,v)/(v,b)` at `e_c/e_a/e_b`, the IH selector off them), with the extensor agreements
  discharged from the IH recording. No `Function.update`-congruence lemma is needed *for W9*
  (M₁/M₂ still need one at the W10 boundary — see (e)). (3) *Sign bookkeeping:* the M₃ candidate
  functional is `ρ̃ := −ρ` (KT (6.44): `Σλ_{(ac)j} r_j(q(ac)) = −r̂`); its three W7 gates convert
  by `LinearMap.neg_apply` (§44 — the negation sits on the functional), `hingeRow_swap`
  (`hingeRow c v (−ρ) = hingeRow v c ρ`), and `panelSupportExtensor_swap`. Notably
  **`candidateRow_ac_eq_neg` is not consumed**: the eq.-(6.43)/(6.44) content arrives through
  the landed **G4d-i** span-induction (`acolumn_mem_hingeRowBlock_of_span_rigidityRows` at
  `wGv := hingeRow a b ρ`, whose `a`-column is `ρ` by `hingeRow_comp_single_tail`), which
  directly yields `ρ ∈ blockFv(e_c)`, i.e. `ρ ⊥ C(q(ac))` — the `hρe₀`-slot.

**Why the loser loses.** The re-derivation route has two readings, both worse. *(B1) Fresh
W6b at the a-split* (`Gab := G.splitOff a v c e₁`, `e₀ := e₁`, rigidity from `ofNormals_relabel`):
its `h622lb` input is `D(m−1) − (D−2) ≤ finrank span((G−a)\text{-rows at } qρ)` — the nested-IH
(6.1) bound at the `k''`-dof `G − a`, **a second undischargeable GAP-6 carry** (the §1.50(b)
dead-end analysis applies verbatim at `a`; the relabel doesn't help — under `σ` the `(G−a)`-rows
correspond to the *v-split-minus-`e_c`* rows, whose bound from `h618` alone is `D(m−1) − (D−1)`,
one short). It would ride to phase close beside the first, doubling the green-modulo surface,
and is KT-unfaithful (KT reuses the same `λ/i^*`; p. 686). *(B2) Re-derive the certify-then-rebase
chain* against `span(a\text{-split rows})` as certificate home: duplicates W6c/W6d/W7
(≈600 lines of the heaviest landed material) for zero reuse, and **still** hits the
`e₁`-elimination — the final step must place every `F(t^*)`-slot in
`span (ofNormals G ends q₀).rigidityRows`, and `e₁ ∉ E(G)`, so the a-split's `e₁`-rows are not
`G`-rows and must be regrouped away exactly as in (1) above. Route B is Route A's transport
leaves plus duplication plus (under B1) a second crux. Verdict: **Route A**, three leaves.

**(b) W9a — the short-circuit-free relabel transport (the span-induction core; CaseI.lean,
beside G4d-i; one commit; no §38).** The G4d-i sibling that transports a v-split-row-span member
across the vertex relabel *with the `e_c`-content stripped*: the `e_c`-generators' images are
exactly `hingeRow v c (generator ∘ single_a)`, so subtracting the `a`-column hinge row makes
every generator land in the `G − a`-row span (off-`a` generators are `swap`-fixed and survive;
`e_c`-generators cancel). Stated abstractly over two `BodyHingeFramework`s (the G4d-i house
style):

```lean
theorem BodyHingeFramework.funLeft_dualMap_sub_acolumn_mem_span_rigidityRows
    [DecidableEq α] {Fv Fva : BodyHingeFramework k α β}
    {v a c : α} {e_c : β}
    (hva : v ≠ a) (hca : c ≠ a) (hcv : c ≠ v)
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
      ∈ Submodule.span ℝ Fva.rigidityRows
```

Proof route: `Submodule.span_induction` with the predicate
`p ψ := (funLeft (swap a v)).dualMap ψ − hingeRow v c (ψ ∘ single a) ∈ span Fva.rigidityRows`
(linear in `ψ`; `zero/add/smul` by submodule closure + `map_add`/`map_smul`/`LinearMap.add_comp`).
Generator `hingeRow x y r` at link `f`, by the G4d-i endpoint case split: `x = a` → `f = e_c`
(`hdeg2`), `y = c` (link uniqueness vs `hlink_ec`, `hca` kills the flip), image
`hingeRow v c r` (`hingeRow_funLeft_dualMap` + `swap_apply_left` + `swap_apply_of_ne_of_ne hca
hcv`), `a`-column `r` (`hingeRow_comp_single_tail hca.symm`… at `a ≠ c`), difference `0` ✓;
`y = a` symmetric via `hingeRow_swap` (difference again `0`); else the `a`-column is `0`
(`hingeRow_comp_single_off`), `hingeRow v c 0 = 0` (`map_zero`), the image is the generator
itself (`swap` fixes `x, y ∉ {a, v}`, the `v`-side from `hnov`), in `Fva.rigidityRows` by
`htrans` + `Submodule.subset_span`. Consumes: `hingeRow_funLeft_dualMap` (the 365740b
RigidityMatrix half), `hingeRow_swap`, `hingeRow_comp_single_tail/_off`. Consumed by: W9c (at
`φ := hingeRow a b ρ`, giving the `hρGv`-slot). No `\lean` pin (internal infra).

**(c) W9b — the M₃ bottom-row tag transport (per-member; CaseI.lean, after W9a; one commit; §38
exposure mild, mitigations named).** The pointwise conversion of one W6b bottom-family member
from the v-split tag shape to the W7-at-M₃-roles tag shape. Stated at the concrete `ofNormals`
frameworks with the `Gv`-side abstract (W9c passes `G.removeVertex v`) and the target hardcoded
at `G.removeVertex a` / the relabeled seed inline:

```lean
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
          = BodyHingeFramework.hingeRow c v ρ'
```

Proof route, per input tag. *`(ab)`-block tag* (`φ = hingeRow a b ρ'`): image `hingeRow v b ρ'`
(`hingeRow_funLeft_dualMap`, `swap_apply_left`, `b` fixed) → LEFT, the genuine `e_b`-row of the
target: link `removeVertex_isLink.mpr ⟨hG_eb, hva.symm…, hab.symm…⟩` (endpoints `v, b ≠ a`),
block via the `ends₃ e_b = (v,b)` extensor evaluation (`ofNormals_normal` +
`swap_apply_right`/`swap_apply_of_ne_of_ne` reduce the seed to `panelSupportExtensor n_a n_b`)
and `mem_hingeRowBlock_iff.mpr` of the input annihilation. *`Gv`-row tag*, destructure
`⟨f, x, y, hlink, r, hr, rfl⟩` and case on `a ∈ {x, y}` (the G4d-i skeleton, with `hdeg2`
*derived*: `hGv_le` + `hcla`, the `f = e_a` branch killed by link uniqueness vs `hG_ea` + `hnov`):
`x = a` → `f = e_c`, `y = c` → RIGHT with `ρ' := −r` (image `hingeRow v c r = hingeRow c v (−r)`;
annihilation from `r ∈ blockFv(e_c)` at `ends₀ e_c ∈ {(a,c), (c,a)}` (`hrecGv`) via
`panelSupportExtensor_swap` + `LinearMap.neg_apply` — §44, the negation is on the functional);
`y = a` symmetric with `ρ' := r`; else → LEFT, the image is `φ` itself (`swap` fixes
`x, y ∉ {a, v}`), a genuine target row: link survives `removeVertex` (`hGv_le` + endpoints
`≠ a`), block by `ends₃ f = ends₀ f` (`hends₃_off`; `f ∉ {e_a, e_b, e_c}` by link uniqueness
against `hG_ea`/`hG_eb`/`hG_ec` + `hnov` + the case) and the recorded components `∉ {a, v}`
(`hrecGv` + `hnov` + case), where the inline seed reduces to `q`. **§38 note:** all memberships
by explicit link witnesses (the `hrow_mem` idiom); extensor evaluations only through
`toBodyHinge_supportExtensor`/`ofNormals_ends`/`ofNormals_normal` rewrites + `Equiv.swap`
evaluation lemmas — never `whnf` on a carrier. Consumes: `hingeRow_funLeft_dualMap`,
`hingeRow_swap`, `panelSupportExtensor_swap`, `mem_hingeRowBlock_iff`, `removeVertex_isLink`.
Consumed by: W9c (mapped over `j`). No `\lean` pin.

**(d) W9c — the M₃ arm closer `case_III_arm_realization_M3` (CaseI.lean, after W9b; one commit;
§38 exposure mild — the trap lives inside W7).** The W8-pattern instantiation commit, with the
heavier conversions delegated to G4d-i/W9a/W9b. Takes the chain context + the v-split W6b
outputs (the SAME `ρ`/`w` package M₁/M₂ consume — one W6b invocation feeds all three arms, KT
p. 686) + the `u = 2` witness data, concludes the generic motive:

```lean
theorem PanelHingeFramework.case_III_arm_realization_M3
    [Finite α] [Finite β]
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
    -- the candidate line `L'' ⊂ Π(c)`: the `u = 2` discriminator witness
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
        w j = BodyHingeFramework.hingeRow a b ρ') :
    PanelHingeFramework.HasGenericFullRankRealization k G
```

Proof route — `refine case_III_arm_realization (k := k) G (G.removeVertex a) ends₃
(q := fun p => q (Equiv.swap a v p.1, p.2)) …` at the roles `(v, a, b, e_a, e_b, n') :=
(a, c, v, e_c, e_a, n''')` with `ρ̃ := −ρ`, `w̃ := (funLeft (swap a v)).dualMap ∘ w`, then
discharge the 22 hypotheses: *(structural)* `a ∉ V(G−a)` / `c, v ∈ V(G−a)` (`hca`/`hva` +
`left/right_mem`), the two links (`hG_ec`, `hG_ea.symm`), the two `ends₃` evaluations, `heac.symm`,
`hleG` (`removeVertex_isLink.mp`), `hsplitG` from `hcla` (a non-`e_a`/`e_c` link cannot touch
`a`), `hends_Gva`/`hne_Gva` verbatim, `hVone`/`hVcard`/`hwcard` by `vertexSet_removeVertex` +
`Set.ncard_diff`-of-singleton + `omega` (`hV3` makes the ℕ-subtraction sane); *(seed-evaluation)*
every W7 hypothesis mentioning `fun i => qW (x, i)` reduces by `simp only
[Equiv.swap_apply_left, Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne …]` under the
binder (`qρ(c,·) = n_c`, `qρ(v,·) = n_a`) — `hLn`/`hgca` then close the `hLn`/`hgab` slots;
*(candidate functional, `ρ̃ = −ρ`)* `hρgate`-slot by `LinearMap.neg_apply` + `neg_ne_zero` (§44);
`hρe₀`-slot = `(−ρ)(panelSupportExtensor n_c n_a) = 0` from **G4d-i** at `Fv := ofNormals
(G.removeVertex v) ends₀ q`, `Fab := Fv` (`hblock := rfl`), `wGv := hingeRow a b ρ` (its
`a`-column is `ρ`, `hingeRow_comp_single_tail hab`), whose conclusion `ρ ∈ blockFv(e_c)` reads
`ρ ⊥ ±panelSupportExtensor n_a n_c` through `mem_hingeRowBlock_iff` + `hrecGv` at the
`e_c`-link + `panelSupportExtensor_swap` (the `hdeg2/hdeg2r` inputs derive from `hcla` +
`removeVertex_isLink` + link uniqueness vs `hG_ea`); `hρGv`-slot = `hingeRow c v (−ρ) =
hingeRow v c ρ` (`hingeRow_swap`) `∈ span((G−a)\text{-rows})` from **W9a** at `φ := hingeRow a b
ρ` (image `hingeRow v b ρ`, `a`-column `ρ`; `htrans` discharged by the same recording/extensor
computations as W9b's off-case) — `hingeRow v b ρ − hingeRow v c ρ ∈ span`, and `hingeRow v b ρ`
is itself the genuine `e_b`-row (`hρe₀` + `hends₃_eb`), so `Submodule.sub_mem` closes;
*(bottom)* `hw̃ := hw.map' _ (LinearMap.ker_eq_bot.2 (LinearMap.dualMap_injective_of_surjective
(LinearMap.funLeft_surjective_of_injective … (Equiv.injective _))))` — `funLeft` of the swap is
surjective since the swap is injective — and `hwmem̃ j := W9b … (hwmem j)`. **§38:** no new
carrier; the swap-evaluation `simp only` set + the `hrow_mem` idiom; the W7-internal trap is
already mitigated inside W7. Consumes: W7, W9a, W9b, G4d-i, `hingeRow_funLeft_dualMap`,
`hingeRow_swap`, mathlib `funLeft`/`dualMap` injectivity. Consumed by: W10 (`u = 2` branch).
No `\lean` pin.

**(e) Consumption/supersession ledger (honesty pass) + the W10 boundary note.**

* **Consumed by the live W9 route:** W7, W6b's outputs, G4d-i, `hingeRow_funLeft_dualMap` (the
  365740b RigidityMatrix half), `hingeRow_swap`, `hingeRow_comp_single_tail/_off`,
  `panelSupportExtensor_swap`, `mem_hingeRowBlock_iff`, the `removeVertex` API, mathlib
  `funLeft`/`dualMap`.
* **Landed but OFF the live route** (stay as green blueprint-pinned nodes documenting KT
  (6.31)/(6.44); do not route new work through them): `mem_span_rigidityRows_ofNormals_relabel`
  (the 365740b CaseI half — its `span(a\text{-split rows})` target is the wrong home: the
  `e₁`-block cannot be stripped from a forgetful span membership post hoc; W9a replaces it),
  `rigidityRows_ofNormals_relabel`, `ofNormals_relabel` (all four conjuncts — the a-split
  framework, its rigidity, and the `e₁`-freshness plumbing never enter the live chain),
  `hasGenericFullRankRealization_of_splitOff_relabel`, G4d-ii
  (`hingeRow_acolumn_mem_span_rigidityRows` — its v-split-span conclusion is bypassed by W9a's
  direct `G − a`-span transport), and `candidateRow_ac_eq_neg` (its (6.44) content arrives via
  G4d-i). **Phase-close obligation:** the blueprint re-read must make the M₃ prose
  (case-iii.tex: `lem:case-III-claim612-eq644`, `lem:splitOff-ofNormals-relabel`,
  `lem:splitOff-rigidityRows-relabel`) describe the (6.39)-transport route and keep those nodes
  as *stated-fact* documentation of KT (6.31)/(6.44), with no live `\uses`-route claiming the W9
  chain routes through them (the supersession gate).
* **GAP-6 surface unchanged:** W9a/W9b/W9c are GAP-6-clean; the single `h622lb` stays on
  W6b/W10 only.
* **W10 boundary pre-brick (flagged now, designed at the W10 moment):** M₁/M₂'s W7 feed consumes
  `hρGv`/`hwmem` at the *overridden* selector `ends' := update² ends₀` while W6b emits them at
  `ends₀`; since `rigidityRows`/`IsInfinitesimallyRigidOn` read `ends` only at linked edges and
  `e_a, e_b` are not `G − v`-links, one small row-set congruence lemma (`ofNormals`-`rigidityRows`
  agrees under selectors equal on links) discharges it. W9 does not need it (W9a/W9b conclude at
  `ends₃` directly); budget it inside W10's commit or as a micro-leaf before it.

**(f) The corrected build order (refines §1.51(j)'s W9 slot; each item one commit).**
~~W1–W8~~ (landed) → **W9a** (the span-induction transport core; leftmost buildable leaf — only
landed inputs) → **W9b** (the per-member bottom tag transport) → **W9c** (the M₃ arm closer) →
**W10** (dispatch + discharge assembly per §1.51(i), + the ends-congruence pre-brick of (e)) →
Leaf 4 → Leaf 5, phase close **green-modulo-GAP-6**. Dependency edges: W9c ← {W9a, W9b, W7,
G4d-i}; W9a ∥ W9b (order between them free; W9a first as the deeper risk). The pinned signatures
fix the mathematical content; instance-set adjustments and small hypothesis-form tweaks
(e.g. carrying `hebc`, or `hwcard` at an equivalent `ncard` form) demanded by elaboration are at
the builder's discretion and are not design deviations.

### 1.53 The W10 design-settle pass — W10's exact signature pinned (one new lemma `case_III_candidate_dispatch` + the ends-congruence pre-brick `rigidityRows_ofNormals_congr_ends`, two commits W10a/W10b); PLUS three §1.51(i) corrections surfaced at the signature level: (1) the recorded-order case split must NOT rename `(a, b)` — the chain roles are asymmetric (the discriminator's `u`-dispatch is pinned to chain order), the fix is a one-time sign/swap NORMALIZATION of the W6b outputs (`ρ̂ := ±ρ`, the landed W8 conversion pattern); (2) the GAP-6 carry cannot enter W10 at a fixed seed (the seed is existentially bound inside `hsplitGP`) — it enters as a QUANTIFIED, IH-conditioned hypothesis; (3) the M₃ branch needs a THIRD selector override (at `e_c`), not two — per-arm selectors differ (2026-06-11)

> **Docs-only design pass (the §1.51(i)/§1.52(e) W10 build-out).** Lean read this pass
> (declarations, current line numbers): CaseI.lean — the producer + `hcand` site
> (`case_III_hsplit_producer` :5252, `hcand` :5272–:5281, application :5330), W6b
> `exists_candidateRow_bottomRows_of_rigidOn` (:3357, signature + the W5-call head), W7
> `case_III_arm_realization` (:4549, full hypothesis list + the (i)–(iii) head mechanics), W8
> `case_III_arm_realization_M2` (:4794, the full conversion bodies :4826–:4847), W9c
> `case_III_arm_realization_M3` (:6072, full body — the `case`-block discharge pattern, the
> `hsplitG`-from-`hcla` block, the `hqρc/hqρv` seed evals), the `hQeq` unpack idiom
> (`hasGenericFullRankRealization_of_splitOff_relabel` :5613–:5627, incl. the `hrec'` Prod-eq
> repackaging), the triple-LI bridge `linearIndependent_normals_of_algebraicIndependent` (:6298,
> **private**, file tail), GAP-2 `hasGenericFullRankRealization_of_rigidOn_ofNormals` (:1971);
> RigidityMatrix.lean — `rigidityRows` (:905 — `ends`-free; `ends` enters only through
> `supportExtensor`), `mem_hingeRowBlock_iff` (:1680), `hingeRow_swap` (:837),
> `exists_homogeneousIncidence_of_normals` (:455), the W1 discriminator
> `exists_complementIso_ne_zero_of_homogeneousIncidence` (:2247), `screwDim` (:74);
> PanelHinge.lean — `IsGeneralPosition` (:121 — quantifies over ALL `a b : α`, not `V(G)`),
> `supportExtensor_ne_zero_of_isGeneralPosition` (:132), `toBodyHinge_supportExtensor` (:95),
> `ofNormals` + `ofNormals_{graph,ends,normal}` (:253–:269 — `ofNormals` is the eta-constructor,
> so `hQeq` is `rfl` after `← hQg`), `HasGenericFullRankRealization` (:1033, the five conjuncts);
> PanelLayer.lean — `panelSupportExtensor_eq_complementIso_extensor` (:330, the `:365` `← rw`
> consumption pattern), `panelSupportExtensor_swap`/`_ne_zero_iff` (:255/:242); Operations.lean —
> `splitOff`/`splitOff_isLink` (:579/:619), `removeVertex_isLink`/`vertexSet_removeVertex`
> (:545/:540), `vertexSet_splitOff` (:604). KT: no new claims this pass — the (6.29)/(6.30)/(6.41)
> one-redundancy sharing (p. 686), the `u`-dispatch (§1.50(a)), and the M₂/M₃ sign conventions
> ride on the §1.50/§1.52 verified reads (model-experiment row 20 + the §1.52 pp. 687–689 re-read);
> every §1.53 correction is Lean-bookkeeping-level. No `.lean`/`.tex` edits this pass.

**(a) Three §1.51(i) corrections (signature-level scrutiny; each would have blocked or mis-routed
the builder).**

1. **The recorded-order case split must not rename `(a, b)`.** §1.51(i) said `e₀` "keeps its
   recorded pair, *possibly in either order* … W10 case-splits and feeds the arms with `(a, b)`
   named in recorded order". Feeding the arms at swapped names is wrong: the chain roles are
   **asymmetric** (`a` carries the `e_c`-edge to `c`; the discriminator's normal family is pinned
   at the chain order `![n_a, n_b, n_c]`, so `u = 0` *means* Π(a), `u = 1` Π(b), `u = 2` Π(c) —
   renaming `a ↔ b` per recorded order desynchronizes the `u`-dispatch from the arms, and the M₃
   branch breaks outright since `hcla`/`e_c` do not swap). The correct move is the landed **W8
   conversion pattern** applied once at the W6b boundary: `rcases hQrec e₀ a b he₀ab` and
   **normalize the W6b outputs to the chain-order `(a, b)`-shapes** — recorded `(a, b)`: take
   `ρ̂ := ρ` and the tags as emitted; recorded `(b, a)`: take `ρ̂ := -ρ` with
   `hingeRow b a ρ = hingeRow a b (-ρ)` (`hingeRow_swap` :837), the annihilations via
   `panelSupportExtensor_swap` + `LinearMap.neg_apply` (§44 — the negation sits on the
   functional), and each `hwmem` `ρ'`-tag converted to `-ρ'` (verbatim the W8 `hwmem` block
   :4843–:4847). After normalization all three arms consume the **same** `ρ̂`/`w`/tag package —
   W7 :4565–:4576, W8 :4811–:4823, and W9c :6094–:6106 state their
   `hρe₀`/`hρGv`/`hwmem` slots **identically** at `q(a,·)/q(b,·)/hingeRow a b`, so the
   normalization is done once, before the discriminator, and the dispatch is uniform.
2. **The GAP-6 carry enters W10 quantified, not at a fixed seed.** §1.51(c) said `h622lb` "next
   appears on W10's signature", but W10 consumes it at the seed/selector pair `(Q.ends, Q.normal)`
   that is **existentially bound inside `hsplitGP`** — a fixed-parameter `h622lb` hypothesis is
   unstatable at W10's level. The carry must be **universally quantified over `(ends, q)` and
   conditioned on the IH-suppliable facts** (the antecedent closure W10 can instantiate from the
   unpacked IH: link-recording, seed-level general position, ℚ-algebraic independence) — exact
   form in (c). The same quantified shape rides up to Leaf 4 (whose wiring lambda binds
   `v a b e₀` and must supply the carry from its own fully-quantified top-level `h622`
   hypothesis); this is where "22h closes green-modulo one hypothesis" becomes concrete. If the
   successor sub-phase's discharge needs a different antecedent set, adjusting it is a two-site
   internal-infra signature change (W10 + Leaf 4, no `\lean` pins), not a re-route.
3. **The M₃ branch needs a third selector override.** §1.51(i)'s "override the selector at the
   two re-inserted hinges" is right for M₁/M₂ but not M₃: W9c requires `ends₃ e_c = (a, c)`
   *exactly* (:6082), while `e_c ∈ E(Gab)` is recorded by `Q.ends` only up to swap. So W10 builds
   **two selectors**: `ends₁ := Function.update (Function.update Q.ends e_a (v, a)) e_b (v, b)`
   for the M₁/M₂ arms, and `ends₃ := Function.update (Function.update (Function.update Q.ends
   e_c (a, c)) e_a (a, v)) e_b (v, b)` for M₃ (note M₃'s `e_a`-value is `(a, v)`, not `(v, a)` —
   W9c :6082). The `ends₃` update evaluations need `e_b ≠ e_c`, which `hcand` does not carry —
   derive `hebc` from link uniqueness (`hleb.eq_and_eq_or_eq_and_eq hlec` puts `v ∈ {a, c}`,
   against `hav`/`hcv`), the §1.52(f)-anticipated tweak.

**(b) The ends-congruence pre-brick — leaf W10a (CaseI.lean, file tail before W10; one commit; no
§38; independently buildable NOW).** The §1.52(e)-deferred brick, scoped tighter than flagged
there: of the four selector-dependent W7 inputs, **only `hρGv` and `hwmem` need it** (they are
W6b *outputs stated at `Q.ends`*, to be consumed at `ends₁`); `hends_Gv`/`hne_Gv` are
*discharged directly at `ends₁`* (for any `Gv`-linking edge `e`, `e ∉ {e_a, e_b}` — the W7-body
`hGv_off` pattern :4611 — so `ends₁ e = Q.ends e` by two `Function.update_of_ne` and `hQrec`
applies; no row-set lemma involved). W9c needs no congruence anywhere (it consumes
`hρGv`/`hwmem`/`hrecGv` at `ends₀ := Q.ends` directly, :6080/:6098/:6103). Since `rigidityRows`
(:905) quantifies over links and reads `ends` only through `(ofNormals …).toBodyHinge.
supportExtensor e = panelSupportExtensor (q ((ends e).1, ·)) (q ((ends e).2, ·))`, selectors equal
on links give *equal* row sets:

```lean
-- CaseI.lean, beside the relabel row-set lemmas (the `rigidityRows_ofNormals_relabel` precedent).
theorem PanelHingeFramework.rigidityRows_ofNormals_congr_ends
    {G : Graph α β} {ends ends' : β → α × α} (q : α × Fin (k + 2) → ℝ)
    (hagree : ∀ e u v, G.IsLink e u v → ends e = ends' e) :
    (PanelHingeFramework.ofNormals G ends q).toBodyHinge.rigidityRows
      = (PanelHingeFramework.ofNormals G ends' q).toBodyHinge.rigidityRows
```

Proof route: `Set.ext φ`; each direction destructures `⟨e, u, v, hlink, r, hr, rfl⟩` and
re-provides the same witness — `φ = hingeRow u v r` is `ends`-free, and the block membership
transports through `mem_hingeRowBlock_iff` (:1680) + `toBodyHinge_supportExtensor` +
`ofNormals_normal`/`ofNormals_ends` + `rw [hagree e u v hlink]` (or its `.symm`). Graph-free over
the carrier (no `whnf`; the established eval-lemma discipline). Consumed by: W10's M₁/M₂ branches
(`rw` into the normalized `hρGv` and into each `hwmem` LEFT disjunct — both span- and set-level
memberships rewrite, the equality is of the underlying row *set*). No `\lean` pin (internal
infra). **Verdict on §1.52(e)'s "budget inside W10 or as a micro-leaf": its own micro-leaf
commit** — it is independently buildable now, and W10 is already the largest assembly of the
suite (see (e)).

**(c) W10 — the dispatch + discharge assembly `case_III_candidate_dispatch` (CaseI.lean, file
tail after the triple-LI bridge; one commit; §38 exposure moderate, mitigations in (e)).**
Matches `hcand`'s parameter shape (:5272–:5281) plus `hsimple` (available at the Leaf-4 wiring
site — the producer's own premise list) plus the quantified GAP-6 carry; concludes the generic
motive, so the Leaf-4 wiring lambda is the positional application
`fun v a b c eₐ e_b e_c e₀ hvG haG hbG hcG hav hbv hba hcv hca hbc heab heac hlea hleb hlec hclv
hcla he₀ hsplitGP => case_III_candidate_dispatch G v a b c eₐ e_b e_c e₀ hsimple hvG … (h622 …)
hsplitGP`:

```lean
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
    -- IH-suppliable facts ((a)2). Instantiated inside the proof at `(Q.ends, Q.normal)`; fed to
    -- W6b as its `h622lb`. An explicit named hypothesis, never a `sorry`.
    (h622lb : ∀ (ends : β → α × α) (q : α × Fin 4 → ℝ),
      (∀ e u w, (G.splitOff v a b e₀).IsLink e u w → ends e = (u, w) ∨ ends e = (w, u)) →
      (∀ x y : α, x ≠ y → LinearIndependent ℝ ![fun i => q (x, i), fun i => q (y, i)]) →
      AlgebraicIndependent ℚ q →
      screwDim 2 * (V(G.splitOff v a b e₀).ncard - 1) - (screwDim 2 - 2)
        ≤ Module.finrank ℝ (Submodule.span ℝ
            (PanelHingeFramework.ofNormals (G.removeVertex v) ends
              q).toBodyHinge.rigidityRows))
    (hsplitGP : PanelHingeFramework.HasGenericFullRankRealization 2 (G.splitOff v a b e₀)) :
    PanelHingeFramework.HasGenericFullRankRealization 2 G
```

No `[DecidableEq α/β]` in the statement (the `Function.update`/`Equiv.swap` terms appear only in
the proof — open with `classical`). `Fin 4`/`Fin (2 + 2)` and `screwDim 2`-vs-`6` are defeq
(`screwDim` :74 is an abbrev; `2 ≤ screwDim 2` closes by `norm_num`); the carry's antecedent set
{link-recording, seed-GP, alg-indep} is the IH-suppliable closure of what the §1.50(b)
footnote-6 discharge consumes (`finrank_infinitesimalMotions_le_of_rankPolynomial_
algebraicIndependent`, no `hspan`). No `\lean` pin (internal infra, the W-suite pattern).

**(d) The proof route — every step against landed signatures.** Names: `Gab := G.splitOff v a b
e₀`, `Gv := G.removeVertex v`, `n_a/n_b/n_c := fun i => q (a/b/c, i)`.

1. **Unpack** `obtain ⟨Q, hQg, hQgp, hQrig, hQrec, hQalg⟩ := hsplitGP`; `q := fun p => Q.normal
   p.1 p.2`; the `hQeq` idiom (:5615, `rw [← hQg]; rfl`) re-expresses `Q` as `ofNormals Gab
   Q.ends q` and rewrites `hQgp`/`hQrig` onto it (`hgp'`/`hrig'` :5617–:5621); repackage `hQrec`
   to Prod-eq form (`hrec'` :5622–:5627).
2. **Inline graph facts:** `he₀ab : Gab.IsLink e₀ a b` (`splitOff_isLink` right disjunct, from
   `hav`/`hbv`/`haG`/`hbG`); `hle : ∀ e u w, Gv.IsLink e u w → Gab.IsLink e u w`
   (`removeVertex_isLink.mp` + left disjunct, `e ≠ e₀` from `e ∈ E(G)` vs `he₀`); `hsplit :
   Gab-link → Gv-link ∨ e = e₀` (disjunct-wise, `removeVertex_isLink.mpr`); `hGv_off : a
   Gv-linking edge is ∉ {e_a, e_b}` (the :4611 pattern); `hV4 : 4 ≤ V(G).ncard` (the four
   pairwise-distinct members `v,a,b,c`, `Set.ncard_insert_of_not_mem` chain ≤ `Set.ncard_le_
   ncard`); `hcard : V(Gab).ncard = V(Gv).ncard` (both sets are `V(G) \ {v}` —
   `vertexSet_splitOff`/`vertexSet_removeVertex`); seed-GP transfer `hgp_seed : ∀ x y, x ≠ y →
   LinearIndependent ℝ ![fun i => q (x, i), fun i => q (y, i)]` from `hQgp` (`IsGeneralPosition`
   :121 quantifies over all `α`; `fun i => q (x, i)` is eta-defeq to `Q.normal x`).
3. **W6b, ONE invocation** at `(Gab, Gv, Q.ends, q, e₀)`: `hD` numeric; `huv : (Q.ends e₀).1 ≠
   (Q.ends e₀).2` by `rcases hrec' e₀ a b he₀ab` (both orders give `≠` from `hba`); `hne₀` via
   `supportExtensor_ne_zero_of_isGeneralPosition` at `hgp'` + `ofNormals_ends`-rewritten `huv`;
   `he₀ : Gab.IsLink e₀ (Q.ends e₀).1 (Q.ends e₀).2` from `he₀ab` + `hrec'` + `IsLink.symm`;
   `hle`/`hsplit`/`hnev := ⟨a, …⟩`/`hrig := hrig'` from step 2/1; **`h622lb := h622lb Q.ends q
   hrec' hgp_seed hQalg`** (the single GAP-6 consumption). Output: `ρ`, `w : Fin (screwDim 2 *
   (V(Gab).ncard − 1)) → _`, `hρne`, `hρe₀'`, `hρGv'`, `hw`, `hwmem'` — all at
   `(Q.ends e₀).1/.2`-endpoints and `Q.ends`-row-sets.
4. **Normalize ((a)1):** `rcases hrec' e₀ a b he₀ab` — recorded `(a, b)`: `ρ̂ := ρ`, facts by
   `rw`; recorded `(b, a)`: `ρ̂ := -ρ`, convert by `hingeRow_swap` + `panelSupportExtensor_swap` +
   `LinearMap.neg_apply`/`map_neg` (§44), tags to `-ρ'` (the W8 :4843–:4847 block). The
   `supportExtensor e₀`-form annihilation becomes the `panelSupportExtensor n_a n_b`-form via
   `toBodyHinge_supportExtensor` + `ofNormals_normal`/`ofNormals_ends` + the recorded-pair `rw`.
   After this point: `hρ̂ne : ρ̂ ≠ 0`, `hρ̂e₀ : ρ̂ (panelSupportExtensor n_a n_b) = 0`, `hρ̂Gv :
   hingeRow a b ρ̂ ∈ span (ofNormals Gv Q.ends q)…rigidityRows`, `hŵmem : ∀ j, w j ∈ (ofNormals
   Gv Q.ends q)…rigidityRows ∨ ∃ ρ', ρ' (panelSupportExtensor n_a n_b) = 0 ∧ w j = hingeRow a b
   ρ'` — the exact common arm shape.
5. **Discriminator:** `hn : LinearIndependent ℝ ![n_a, n_b, n_c]` :=
   `linearIndependent_normals_of_algebraicIndependent hQalg hba.symm hca.symm hbc` (private,
   same file — forces W10's placement after it); `obtain ⟨pbar, hp, h0, h1, h2, h3⟩ :=
   exists_homogeneousIncidence_of_normals hn` (:455; project away the `≠ 0` third conjuncts);
   `obtain ⟨u, n', hpair, hgate⟩ := exists_complementIso_ne_zero_of_homogeneousIncidence hρ̂ne hp
   hn h0 ⟨h1.1, h1.2.1⟩ ⟨h2.1, h2.2.1⟩ ⟨h3.1, h3.2.1⟩` (:2247); bridge `rw [←
   panelSupportExtensor_eq_complementIso_extensor] at hgate` (:330, the :365 pattern) — `hgate :
   ρ̂ (panelSupportExtensor (![n_a, n_b, n_c] u) n') ≠ 0`.
6. **Dispatch** `fin_cases u` + `simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
   Matrix.head_cons, …]` at `hpair`/`hgate`, then per arm. **Common feeds** (all three arms):
   `hvVc/haVc/hbVc`-slots by `vertexSet_removeVertex` + memberships/distinctness; `hVone`/
   `hVcard`/`hwcard`-slots by `hcard` + `hV4` + `Nat.card`-of-`Fin` + `omega`; `hw` verbatim;
   `ρ := ρ̂` and the normalized `hρ̂e₀`/`hρ̂Gv`/`hŵmem` (M₁/M₂ after the (b) congruence `rw`; M₃
   as-is). Per arm:
   * **`u = 0` → W7** at `(G, Gv, ends₁, q, v, a, b, e_a, e_b, n')`, `ends₁` per (a)3:
     `hends_ea/hends_eb` by `Function.update_self`/`_of_ne heab`; `hG_ea/hG_eb := hlea/hleb`;
     `hleG := removeVertex_isLink.mp ∘ ….1`; `hsplitG` from `hclv` (endpoint-`v` case) +
     `removeVertex_isLink.mpr` (the W9c `hsplitG`-block mirror at `hclv`); `hends_Gv` — for a
     `Gv`-link, `e ∉ {e_a, e_b}` (`hGv_off`), so `ends₁ e = Q.ends e` (two `update_of_ne`), then
     `hle` + `hQrec` + `IsLink.symm`; `hne_Gv` — same reduction to `Q.ends e`, endpoints distinct
     (`hsimple` → loopless, transported through `removeVertex_isLink`), then
     `supportExtensor_ne_zero_of_isGeneralPosition` at the GP-transferred `ofNormals Gv ends₁ q`
     (step-2 `hgp_seed` shape) + `ofNormals_ends`; `hLn := hpair`; `hgab := hgp_seed a b
     hba.symm`-eta; `hρgate := hgate`; **`hρGv`/`hwmem` via the (b) congruence**: `rw
     [PanelHingeFramework.rigidityRows_ofNormals_congr_ends q (fun e u w hl => (two
     update_of_ne via hGv_off))] at hρ̂Gv hŵmem`-style (one direction; the lemma's `hagree` is
     stated `Q.ends → ends₁`, supply `.symm` as needed).
   * **`u = 1` → W8** at the same `(G, Gv, ends₁, q, v, a, b, e_a, e_b)`, `n'' := n'`: identical
     feeds (W8's hypothesis list :4794–:4823 is W7's with only `hLn`/`hρgate` moved to the
     `b`-side — exactly `hpair`/`hgate` at `u = 1`); W8 performs the internal `-ρ̂` swap itself.
   * **`u = 2` → W9c** at `(G, ends₀ := Q.ends, ends₃, q, v, a, b, c, e_a, e_b, e_c)`,
     `n''' := n'`, `ends₃` per (a)3 (needs `hebc`): `hva/hab/hvb/hca/hcv` from the distinctness
     pack (`.symm` as needed); `hG_ea/hG_eb/hG_ec := hlea/hleb/hlec`; `heac`; `hcla` verbatim;
     `hrecGv := fun e x y hl => hrec' e x y (hle …)`; the three `hends₃` evals + `hends₃_off` by
     update evaluations (`hebc`, `heac`, `heab`); `hends_Gva` — case `e = e_b`:
     `removeVertex_isLink.mpr ⟨hleb, hav.symm, hba⟩` at `ends₃ e_b = (v, b)`; cases `e = e_a`/
     `e = e_c`: vacuous (their `G`-links touch `a`, so no `G − a`-link survives — link
     uniqueness); off-case: `ends₃ e = Q.ends e`, the link avoids `a` and (via `hclv`, since
     `e ∉ {e_a, e_b}`) avoids `v`, hence is a `Gv`-link → `hle` + `hrec'` + `IsLink.symm`;
     `hne_Gva` — same case analysis, extensor evals at the inline relabeled seed via
     `toBodyHinge_supportExtensor` + `ofNormals_normal` + `Equiv.swap` evaluation lemmas, nonzero
     from `hgp_seed` at the swap-injected distinct pair; `hV3` from `hV4`; `hLn := hpair`;
     `hgca := hgp_seed c a hca`-eta; `hρgate := hgate`; `hρe₀/hρGv/hwmem` := the step-4
     normalized facts **as-is** (W9c consumes at `Q.ends`; no congruence); `hwcard` by `hcard` +
     `Set.ncard_diff_singleton_of_mem hvG` + `omega` (with `hV4`).

   Each arm concludes `HasGenericFullRankRealization 2 G` — the goal. No leftover obligations;
   GAP-2 and the §38-heavy mechanics live inside the arms.

**(e) Leaf cut + §38 exposure.** **Two commits**: **W10a** = (b) alone (independently buildable
now, no dependencies beyond landed API); **W10b** = (c)/(d) whole (the dispatch lemma; all
remaining work is hypothesis-feeding against pinned signatures — no sub-leaf is independently
meaningful, and the per-arm feeds are each ≤ a few tactics given (d)). No `sorry` at any point;
the only carried hypothesis is the quantified `h622lb` (consumed at step 3, never discharged
in-phase). §38 exposure in W10b, per step: *step 1/3* — the `hQeq` idiom only (never unfold
`ofNormals`/`toBodyHinge`; the :5613–:5627 pattern verbatim); *step 4* — pure rewrites through
the three eval lemmas (`toBodyHinge_supportExtensor`, `ofNormals_normal`, `ofNormals_ends`) +
swap lemmas, never `whnf`; *step 6* — the arm `refine`s carry concrete `Function.update`
selectors and the heavy `w`-family as explicit arguments: `set ends₁ := … with hends₁` / `set
ends₃ := … with hends₃` before the `refine` (keep the body, the update-evals need it — do NOT
`clear_value` these), discharge hypotheses in named `case` blocks (the W9c :6160–:6164 pattern);
if an arm application itself `whnf`-times-out on the `w`-argument, `set f := w; clear_value f`
first (TACTICS-QUIRKS §38, *Row-family-argument variant* — the W7-internal mitigation, applied
at the call site). Mind §43 (`set` folding pre-existing hypotheses — name the `set`s before
obtaining facts that mention their bodies, or `rw [hends₁]` explicitly) and §4 (no `rcases …
rfl` on the recorded-pair equations near `e_a`/`e_b`; use named equations + `rw`, the W7
dispatch discipline).

**(f) Build order (refines §1.51(j)/§1.52(f)'s W10 slot; each item one commit).**
~~W1–W9c~~ (landed) → **W10a** (the congruence pre-brick) → **W10b** (`case_III_candidate_
dispatch`) → **Leaf 4** (the `theorem_55_generic (n := 2) (k := 2)` instance; its wiring lambda
is the (c) positional application, and the leaf's statement gains the **fully-quantified GAP-6
hypothesis** — quantifying additionally over `(v, a, b, e₀)` and, per its wiring shape, the
graph — whose exact form is pinned at the Leaf-4 moment from (c)'s per-instantiation form) →
**Leaf 5** → phase close **green-modulo-GAP-6**. The pinned signatures fix the mathematical
content; instance-set adjustments and small hypothesis-form tweaks demanded by elaboration are at
the builder's discretion and are not design deviations.

---

## 3. Per-case producer structure, node list, build order

Honesty gate applied: each node tagged **buildable** (math settled, arithmetic
closes from green inputs — decompose-then-build) or **research-shaped** (the
math is the hard part — math-first before any node is scheduled), per `DESIGN.md`
*Constructibility recon …*.

### Track A — Case I producer (`hcontract`), KT §6.2

KT splits Case I into three sub-cases by simplicity. The **constructibility
arithmetic closes for all three**: `rank = D(|V'|−1) [rigid block] + D(|V∖V'∪{v*}|−1)−k [contraction] = D(|V|−1)−k` (eqs. 6.3, 6.9), full rank at k=0. No
shortfall — this is the tractable track.

Nodes (composing the green infra of §2):

- **N6a — non-simple Case I (KT Lemma 6.2).** **GREEN** (2026-06-04). Equal-panel
  splice (`ΠG/E',p2(v*) = ΠG',p1(a) = ΠG',p1(b)`); a bare (non-general-position)
  realization suffices, so it consumes the *bare* motive and supplies the bare
  motive. Built as `hasFullRankRealization_of_splice_of_supportExtensor`
  (+ leg-native `…_ofNormals`): the splice producer parameterized by transversal
  hinges (`hsupp`) directly rather than general position (`hgp`) — N7b-0 only ever
  needed `hsupp`. The old `hasFullRankRealization_of_splice` now factors through it
  as a thin GP corollary. Lowest-risk starting node; **does not need the motive
  strengthening** — confirmed in practice (axiom-clean, no Phase-20 touch).
- **N6b/N6c — simple Case I (KT Lemma 6.3/6.5).** **GREEN** (2026-06-04;
  `hasFullRankRealization_of_couple_ofNormals`). The shared-seed coupling: each
  leg's leg-restricted rank polynomial × the (G2) factor → triple-product shared
  non-root → each leg rigid + GP at it → `…_splice_ofNormals`. *Note:* this
  concludes only the **bare** motive — the GP is held at the seed `q₀` but the
  device realizes at a different hidden `q` (see §1.5); upgrading it to conclude
  `HasGenericFullRankRealization` is N6-G1.
- **(G2) general-position factor.** **GREEN** (2026-06-04;
  `exists_generalPosition_polynomial`). Off-diagonal product of leading `2×2`
  minor polynomials, witnessed nonzero at the moment-curve seed (Vandermonde).
- **N6 — Case I composer (`lem:case-I-realization`).** **RED — decomposed in §1.5
  into the hybrid N6-G1/G2/G3; N6-G1/G2 (G2a/G2b/G2c) now GREEN.** Not `buildable`
  as a single commit: the composer's adapter needs each leg in
  `HasGenericFullRankRealization`, which (i) the coupling did not produce — **fixed
  by N6-G1, GREEN** — and (ii) `minimal_kdof_reduction` does not thread (N6-G2,
  Route 1, re-reconned in §1.6 into G2a/G2b/G2c, **all GREEN**). **Remaining: N6-G3's
  G3b/G3c** (re-reconned in §1.7 into G3a/G3b/G3c; **G3a now GREEN-MODULO**, 2026-06-05).
  The composer is NOT pure leg-data geometry: the contraction leg's rigidity is
  transported across the collapse map by G3a `rigidContract_rigidity_transport` (KT
  Claim 6.4, carried as the explicit hypothesis `htransport` — green-modulo, axiom-
  clean); then the cover/simplicity geometry (G3b, buildable) and the assembly/flip
  (G3c, buildable). See §1.7 + `notes/Phase22a.md`.

**Build order (Track A), updated 2026-06-05 (G3a green-modulo; G3b is the next build):**
§1 motive decision ✓ → N6a ✓ → (G2) ✓ → N6b/N6c coupling ✓ → **N6 composer
(§1.5 hybrid, §1.6 N6-G2 cut, §1.7 N6-G3 cut): N6-G1 ✓ → G2a ✓ → G2b ✓ → G2c ✓ →
N6-G3 (G3a ✓ green-modulo → G3b → G3c).**

### Track B — Case II/III producer (`hsplit`), KT §6.3 (Lemma 6.8) + §6.4.1

**This is KT Case III** at the project's k=0 scope (FRICTION dead-end #3; Finding
B; `DESIGN.md` *Phase Case-naming …*). Constructibility: eq. (6.12) degenerate
placement gives `+(D−1)` ⟹ `rank = D(|V|−1)−1`, **one row short** of the k=0 full
target. The missing row is the Case-III redundant-edge row.

- **eq. (6.12) degenerate placement** (`p1(vb)=q(ab)` reproduces the `e₀`
  row). `buildable` (feeds the green N7b-0/1/2/3 + pin-a-body split). Gives
  `+(D−1)`. **Needs the incoming split-leg nonparallel** (Claim 6.4) — so it too
  consumes the strengthened motive (or the two-motive's generic form).
- **Lemma 6.10 (`d=3`, 3 candidates)** — `research-shaped`. The single largest
  proof in KT (~12 pp.). Two sub-claims:
  - **Claim 6.11 (combinatorial↔linear):** `R(G_v^{ab},q)` has a redundant
    `ab`-row, via Lemma 4.3(ii) + IH. Wires `M(G̃_v^{ab})` to the row matroid of
    `R`. The hardest non-extensor step; `research-shaped`.
  - **Claim 6.12 (extensor-span genericity):** if all `D` candidates fail, a
    nonzero `r ∈ ℝᴰ` is ⟂ all extensors on `d+1` generic panels, which by
    **Lemma 2.1** (`omitTwoExtensor_linearIndependent`, green, hyp
    `AffineIndependent ℝ p`) span `ℝᴰ` — contradiction. The degree-2 condition
    forces all candidates to test the same `r` (eq. 6.44). The extensor half maps
    onto Phase-17's Lemma 2.1 directly; `research-shaped` only in the candidate-
    bookkeeping (consider an abstracted "candidate normal form" lemma to avoid
    repeating the row-ops three times).

**Build order (Track B):** strictly *after* Track A and the motive decision. The
eq. (6.12) placement is the buildable warm-up; Lemma 6.10 is the crux and is the
natural decompose-math-first target for a dedicated sub-session.

### Assembly (the `d=3` cut — see §1.33 for the re-scoped recon)

> **Re-scoped 2026-06-07 (§1.33).** Two items below are now done; the real gap is
> narrower than this stub. Read §1.33 (A)/(B) for the current breakdown + open items.

- **`prop:rigidity-matrix-prop11` `hub` brick** — ~~research-shaped~~ **GREEN**: the
  `D + def ≤ dim Z` lower bound (`screwDim_add_deficiency_le_finrank_infinitesimalMotions`)
  is discharged in-proof; `rigidityMatrix_prop11` is green-modulo its `hgen` = Theorem 5.5.
  This stub's deficiency-partition motion count was discharged in 22d.
- **The `d=3` `hsplit` producer** (`lem:case-II-realization` at `k=0`) — **the real gap**:
  wire `case_II_placement_eq612` ⊕ candidate-row ⊕ `case_III_claim612` into the graph-free
  `linearIndependent_sum_augment_candidateRow` at real graph data (where the `ofNormals`
  defeq trap bites). §1.33 (A).
- **`thm:theorem-55` / `lem:case-III` flip green** — once the `hsplit` producer lands,
  instantiate the green conditional `theorem_55 (n:=2)`; the *general* node stays red for
  Phase 23 (architecture call in §1.33 (B.2)). Open item: whether `lem:cycle-realization`
  is Lean-load-bearing for this path (§1.33 (B.1)).

---

## 4. Risk / scope

**Genuinely research-shaped (the math is the hard part):**
- **Lemma 6.10 / Claim 6.11** (Track B) — the largest proof in KT; the
  combinatorial↔linear redundant-`ab`-row identity is the single highest-risk
  node in Phases 22–23. Claim 6.12's extensor half is de-risked (Lemma 2.1 green).
- **`hub` partition-count** — multi-commit but settled math (Phase-19 substrate).
- **(G2) general-position factor** — bounded research-shaped; standard math, new
  Lean mirror.

**Buildable once §1 is decided:** the entire Case-I track (N6a fully motive-
independent; N6b/N6c gated on (G2)+motive), the eq. (6.12) placement, and the
final `theorem_55` flip.

**Axiomatization / deferral candidates, if full formalization of a case proves
out of reach (in escalation order — do not reach for these before the math-first
decomposition is genuinely stuck):**
1. **Lemma 6.10 / Claim 6.11 as an explicit hypothesis on the Case-III node**,
   in the established Phase-21b "carry the analytic crux as `h…` and `\uses` the
   red node" idiom (exactly how Cases I/II carried the device pre-21b). This
   keeps `theorem_55` green-modulo-Lemma-6.10 and honest (the node stays red),
   and is the *recommended* fallback — it isolates the one genuinely-hard kernel
   without blocking the rest of the molecular program (Phases 24–26 depend on
   Thm 5.6, which needs Thm 5.5; a green-modulo capstone unblocks them).
2. **(G2) factor as a hypothesis** on the Case-I composer (same idiom), if the
   Vandermonde brick stalls — lower-risk than (1), since (G2) is bounded.
3. **`theorem_55` itself as `axiom`** — *last resort, not recommended.* It would
   make the whole molecular capstone (Cor 5.7) rest on an axiom; prefer the
   green-modulo decomposition (1)/(2), which keeps every discharged step honest
   and tracks the remaining obligation as a visible red node.

**Scope guard:** the motive decision (§1) is a *prerequisite* to any Case-I
simple-case build or any Track-B build — both consume nonparallel legs. The one
node that needs *nothing* from §1 is N6a (non-simple Case I). A sensible first
commit after the motive decision is N6a (proves out the splice plumbing on the
bare motive), then the (G2) factor, then the simple cases.

---

## 5. One-line recommendation

**Strengthen the motive to carry general position, conditioned on `G.Simple`
(matching KT's "nonparallel, if simple"); prefer the two-motive split if
threading `Simple` through `minimal_kdof_reduction` is costly — this dissolves
gap (G1) at the source, leaves the green producer infra needing only the bounded
(G2) general-position factor for Case I, and isolates the one genuinely
research-shaped kernel (Lemma 6.10 / Claim 6.11, Track B) as a green-modulo
deferral candidate.**
