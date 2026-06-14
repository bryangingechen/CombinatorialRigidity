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

### 1.54 The Leaf-5 feed-audit / design-settle pass — the five carried callbacks audited against the landed Lean; THREE of the hand-off's expectations corrected: (1) `hbase`/`hbaseGP` do NOT come from the Pinning.lean base layer (that layer is framework-level) — `hbaseGP` is VACUOUS (simple ∧ minimal-0-dof ∧ |V|=2 is contradictory, the parallel-pair cut bound) and `hbase` is reachable only through a degenerate-selector realization; (2) that same degenerate brick discharges `hsplit` AND `hcontract` (bare) outright — the bare motive `HasFullRankRealization` carries no genuine-hinge condition and is satisfiable for EVERY connected graph, so the bare conjunct is formally vacuous and the mathematical content of `theorem_55_d3` lives entirely in the GP conjunct (USER SIGN-OFF flagged); (3) `hcontractGP ≠ case_I_realization` alone — the KT 6.3-vs-6.5 dispatch on `(G.rigidContract H r).Simple` is unformalized and the Lemma-6.5 arm (Claim 6.6 + the Π°-placement) is genuinely missing (~4–6 commits, the phase-close-estimate changer); PLUS (b) the Thm 5.5→5.6 push at 22h-close is the `def = 0`/simple/spanning stratum only (full Thm 5.6 needs the all-`k` restructure, the already-adjudicated GAP-6 successor) and (c) the blueprint plan (2026-06-11)

> **Docs-only design pass (the Leaf-5 recon-before-build).** Lean read this pass (declarations,
> current line numbers): CaseI.lean — `theorem_55_d3` (:6752; the five carried hypotheses
> :6755–:6775, the `h622` carry :6779, the wiring :6790–:6800 — `hbase`/`hbaseGP`/`hsplit`/
> `hcontract`/`hcontractGP` pass straight through, conclusion projects `.2`),
> `case_I_realization` (:2089 — hypothesis list `hD : 3 ≤ bodyBarDim n`, `hG`, `{H} hH :
> IsProperRigidSubgraph`, `{r} hr : r ∈ V(H)`, `hVH2`, `hSimple`, **`hcSimple :
> (G.rigidContract H r).Simple`**, conditioned `hIH`; concludes GP), the couple/coupling suite
> (:73/:158/:247), `rankHypothesis_ofNormals_of_rankPolynomial_algebraicIndependent` (:2723, the
> landed prop11 consumer; `exact rigidityMatrix_prop11 F n hn hC hgen` :2773); PanelHinge.lean —
> `HasFullRankRealization` (:979 — `∃ Q, Q.graph = G ∧ rigid-on-V(G)`, **no `ends`/extensor
> condition**), `HasGenericFullRankRealization` (:1033), `hasFullRankRealization_of_generic`
> (:1046), `theorem_55_generic` (:1146; branch lambdas :1182–:1191 — the full conditioned IH is
> in scope in each branch), `rigidityMatrix_prop11` (:1230; `hC : ∀ e, supportExtensor e ≠ 0`
> over ALL of `β`, `hgen` :1233), `PanelHingeFramework` (:65 — `ends : β → α × α` is *free*
> per-edge data; `toBodyHinge.supportExtensor e = panelSupportExtensor (normal (ends e).1)
> (normal (ends e).2)` :89); Pinning.lean — `theorem_55_base` (:630, **framework-level**: takes
> `F : BodyHingeFramework`, two edges, an LI-extensor hypothesis; no graph-level `∀ G` form
> exists anywhere in tree); PanelLayer.lean — `panelSupportExtensor_ne_zero_iff` (:242 — so
> `panelSupportExtensor n n = 0`); Deficiency.lean — `IsKDof` (:350, `deficiency n = k`),
> `IsMinimalKDof` (:359), `loopless_of_isMinimalKDof` (:370), `IsProperRigidSubgraph` (:428 —
> the G5-repaired `2 ≤ V(H).ncard` is conjunct `.2.1`; `.vertexSet_nonempty` :433),
> `two_le_crossingEdges_of_isKDof_zero` (:780), `mulTilde_isLink` (:127),
> `mulTilde_preconnected_of_isKDof_zero` (:817); ReducibleVertex.lean —
> `simple_of_isMinimalKDof_of_noRigid` (:625 — `hD : 2 ≤ bodyBarDim n`, `hV : 3 ≤ ncard`, `hG`,
> `hnp`); Contraction.lean — `rigidContract_simple` (:144 — **conditional** on `hloop`/`hpar`,
> NOT derivable from `IsProperRigidSubgraph + G.Simple`; KT takes `G/E′` simple as a *case
> hypothesis*); GenericityDevice.lean — `hasFullRankRealization_of_splice_of_supportExtensor`
> (:822 — N6a; `hends` quantified over ALL `e : β`, `hsupp : ∀ e, ≠ 0`),
> `finrank_infinitesimalMotions_of_isInfinitesimallyRigidOn_vertexSet` (:431). KT 2011:
> p. 671 (base trichotomy: |V|=2 minimal `k`-dof is (i) `E = ∅`, (ii) one edge, (iii) the
> parallel pair; only (iii) has `k = 0`), p. 673 (Lemma 6.2 + the 6.2/6.3/6.5 trifurcation),
> p. 676–677 (Lemma 6.5 + Claim 6.6, the maximal-rigid-subgraph degree-2 removal + the Π°
> placement), p. 670 (parallel panels at the non-simple leaves; Thm 5.6 + proof:
> `k := def(G̃)`, strip to a minimal `k`-dof spanning subgraph, Thm 5.5 **at `k`**, projective
> move, re-add edges). No `.lean`/`.tex` edits this pass.

**(a) The five-callback feed audit (the §1.41(5) expectations, corrected).**

**(a1) `hbase`/`hbaseGP` — the "Pinning.lean base layer" expectation is WRONG.** Pinning.lean's
`theorem_55_base` (:630) is framework-level (`F : BodyHingeFramework`, two named edges, an
LI-extensor hypothesis); no graph-level producer `∀ G, IsMinimalKDof n 0 → V(G).ncard = 2 → …`
exists in tree (verified: no `HasFullRankRealization` mention in Pinning.lean; tree-wide grep).
The graph-level facts are:

* **`hbaseGP` is VACUOUSLY dischargeable** — a simple two-vertex minimal-`0`-dof graph does not
  exist (KT p. 671: only the parallel-pair case (iii) of the |V|=2 trichotomy is `0`-dof). Lean
  route: from `V(G).ncard = 2` extract `u ≠ v`; `two_le_crossingEdges_of_isKDof_zero` (:780, at
  `V' := {u}`, `hD1 : 1 ≤ bodyBarDim n` by `omega` from the carried `hD`) gives two distinct
  crossing edges; `loopless_of_isMinimalKDof` (:370) + `V(G) = {u, v}` makes both link `u v`;
  `hSimple.eq_of_isLink` collapses them — contradiction. One small lemma (suggest
  `Graph.not_simple_of_isMinimalKDof_of_ncard_two`, ReducibleVertex.lean beside G0) + a
  `fun G hG hV2 hSimple => absurd hSimple …` feed.
* **`hbase` is reachable ONLY through a degenerate-selector realization.** The honest KT-5.3
  content (two independent hinge lines in a common panel) is *inexpressible* in the
  `PanelHingeFramework` model at ambient `|α| = 2`: the structure (:65) has no per-edge hinge
  freedom — `C(e)` is the meet of two body normals at the free selector `ends e` — and with only
  two bodies the available extensors are `{0, ±panelSupportExtensor n_u n_v}`, never an LI pair.
  What IS available: the **degenerate selector** `ends := fun _ => (a₀, a₀)` gives `C(e) =
  panelSupportExtensor n n = 0` (:242, `![n, n]` not LI) for every edge, and the hinge constraint
  `S u − S v ∈ span {0} = ⊥` then *welds* every linked pair — rigidity on a connected `V(G)` is
  immediate. See (a2): this discharges far more than `hbase`.

**(a2) The headline finding — the bare motive is degenerately satisfiable for every connected
graph; ONE brick discharges `hbase`, `hsplit`, AND `hcontract`.** `HasFullRankRealization`
(:979) demands only `∃ Q, Q.graph = G ∧ Q.toBodyHinge.IsInfinitesimallyRigidOn V(G)` — **no
link-recording, no nonzero-extensor condition** (deliberately: the non-simple KT realizations
need off-link selectors, cf. KT 6.2's coincident panels). Consequence, unnoticed until this
audit: take any `a₀ ∈ V(G)`, `Q := ⟨G, 0, fun _ => (a₀, a₀)⟩`; every supporting extensor is `0`,
every link welds its endpoints, and constancy on `V(G)` follows from connectivity — which every
`0`-dof graph has (`mulTilde_preconnected_of_isKDof_zero` :817 + the `mulTilde_isLink` :127
projection of a `G̃`-walk to `G`-links). So:

```lean
-- Deficiency.lean (or PanelHinge.lean beside the motive); the one new brick.
theorem PanelHingeFramework.hasFullRankRealization_of_isKDof_zero
    [Finite α] {G : Graph α β} {n : ℕ} [NeZero (Graph.bodyHingeMult n)]
    (hG : G.IsKDof n 0) (hne : V(G).Nonempty) :
    PanelHingeFramework.HasFullRankRealization k G
```

feeds **all three bare callbacks** of `theorem_55_d3` (each supplies `hG.1 : G.IsKDof n 0` and
nonemptiness from its `ncard` bound; each ignores its IH; the `NeZero` instance is the
established `⟨by rw [Graph.bodyHingeMult]; omega⟩` idiom from `hD`). No `theorem_55_generic`
restructure, no Lemma-6.2 composer, no N6a wiring. **The cost is semantic, and is flagged for
user sign-off rather than decided here:** this makes the bare conjunct of `thm:theorem-55`
mathematically vacuous — the project's `HasFullRankRealization` does not capture KT's "panel-hinge
realization" (whose hinges are genuine `(d−2)`-flats, `C(e) ≠ 0`), and KT Thm 5.5's bare half is
trivially true under it. The *meaningful* content of `theorem_55_d3` then lives entirely in the
GP conjunct (`HasGenericFullRankRealization`, which records links and forces `C(e) ≠ 0` on edges
via GP + looplessness) — which is also the only conjunct the capstone push consumes ((b) below).
Alternatives if the user rejects the degenerate route: strengthen the bare motive with a
genuine-hinge conjunct (`∀ e u v, G.IsLink e u v → C(e) ≠ 0`) — KT-faithful but a cross-phase
restructure (every bare producer/consumer re-proved, incl. the landed Phase-20/21b spine;
~10+ commits and it re-opens the Lemma-6.2/Lemma-5.3 builds the current cut never needed, since
the genuine-hinge bare motive at the parallel-pair base and the non-simple Case I *is* exactly
KT 5.3/6.2, both inexpressible-without-off-link-selector-work as audited above). Middle option:
land the degenerate brick now (it is sound Lean and unblocks the phase) and record the
genuine-hinge strengthening as a named successor obligation next to the GAP-6 one (the all-`k`
restructure will already re-touch the motive; fold both into that re-design moment).
**Recommendation: the middle option** — at `d = 3` the capstone (Cor 5.7, simple square graphs)
never consumes the bare conjunct, so deferring costs nothing now and avoids designing the motive
twice.

**(a3) `hcontractGP` — `case_I_realization` is the 6.3 arm only; the 6.3-vs-6.5 dispatch and the
Lemma-6.5 arm are missing (the estimate changer).** The callback hands `∃ H,
IsProperRigidSubgraph G n` + `G.Simple` + the conditioned IH. `case_I_realization` (:2089)
additionally needs, for the chosen `H` and representative `r`, the **case hypothesis** `hcSimple
: (G.rigidContract H r).Simple` — which is *not* derivable (`rigidContract_simple` :144 is
conditional on `hloop`/`hpar`; KT p. 673 takes `G/E′` simple as Lemma 6.3's case split, routing
its failure to **Lemma 6.5**, the vertex-removal argument — Phase 22a's "the `hcontract`
dispatch is the coordinator's wiring" deferral, never landed). Exact wiring of the 6.3 arm
(thin, once the dispatch supplies `H`, `r`, `hcSimple`):

```lean
fun G hG hV3 hex hSimple hIH =>
  -- dispatch (L5c3) supplies ⟨H, hH, r, hr, hcSimple⟩; then:
  PanelHingeFramework.case_I_realization (by omega) G hG hH hr hH.2.1 hSimple hcSimple hIH
```

(`hD : 3 ≤ bodyBarDim n` by `omega` from `theorem_55_d3`'s `6 ≤`; `hVH2 := hH.2.1`, the
G5-repaired conjunct — the §1.41(3)/(5) "+ `hVH2` from G5" expectation CONFIRMED; `r` from
`hH.vertexSet_nonempty` when the dispatch doesn't pin it.) The **Lemma-6.5 arm** (KT pp.
676–677), needed when *no* `(H, r)` has a simple contraction, decomposes as:

1. **Claim 6.6 (graph side, NEW, ~2–3 commits).** Take a vertex-inclusionwise *maximal* proper
   rigid subgraph `G′`; non-simplicity of `G/E(G′)` yields `v ∈ V ∖ V′` with two edges into
   `V′`; `G″ := G′ + v + {e, f}` is rigid (KT Lemma 4.4's `def(G̃″) ≤ def(G̃′)` — audit Phase-20
   for a landed analog; none surfaced this pass), maximality forces `V = V′ ∪ {v}` and `G = G″`;
   conclusion: `G` is `0`-dof and has a degree-2 vertex `v` with `G − v` minimal `0`-dof and
   *simple* (from `G.Simple`). Genuinely new combinatorics (maximal-subgraph choice + the
   Lemma-4.4 step), but bounded and research-free.
2. **The Π°-placement producer (geometric side, NEW, ~1–2 commits + its own signature pin).**
   From the conditioned IH at `G − v` (simple, smaller, minimal `0`-dof → its GP conjunct):
   realize `G` at the *same* seed `q` — `v` already carries an alg-independent normal `q(v, ·)`
   in the ambient seed, which serves as KT's `Π°` (no extension step needed; KT's two side
   conditions are exactly (i) GP pairs — the seed's GP conjunct — and (ii) the triple
   `![q(v,·), q(a,·), q(b,·)]` LI — the landed triple-LI bridge
   `linearIndependent_normals_of_algebraicIndependent`, §1.53). Selector: `Q_{Gv}.ends`
   overridden at the two `v`-edges (the W10 `Function.update` pattern). Rigidity: a `G`-motion
   restricts to a `Gv`-motion (selector congruence off the `v`-edges, the W10a/W9b discipline),
   so it is constant on `V(G − v)`; the two `v`-hinge constraints `S v − S a ∈ span C(va)`,
   `S v − S b ∈ span C(vb)` with the two extensors LI (from the triple-LI) force `S v = S a` —
   the `eq_of_hingeConstraint_two_parallel` shape (Pinning.lean, the `theorem_55_base`
   workhorse) at distinct far endpoints. GP/link-recording/alg-indep conjuncts: same seed, link-
   recording selector by construction. All bricks are landed; the assembly is new and needs its
   own one-pass signature pin (a §1.53-style block) before building — NOT pinned here, since the
   build is conditional on the user's (a2)/(a3) scope call.
3. **The dispatch (1 commit).** `by_cases hd : ∃ H r, IsProperRigidSubgraph … ∧ r ∈ V(H) ∧
   (G.rigidContract H r).Simple` (classical); positive → the 6.3 arm above; negative → the 6.5
   arm (whose Claim-6.6 needs exactly the negative: every proper rigid subgraph has non-simple
   contraction). Note KT's Claim 6.6 only needs the *maximal* `G′`'s contraction non-simple, so
   the dispatch may equivalently case on that single instance.

**Scope option flagged for the user (changes the phase-close estimate):** (A) build the 6.5 arm
in-phase (+4–6 commits before `hcontractGP` feeds); (B) close 22h green-modulo TWO carried
hypotheses (`h622` + a named `h65 : <the 6.5-stratum hcontractGP instance>`), deferring the 6.5
arm to a successor sub-phase alongside the GAP-6 discharge. (B) is honest (the carry is a
visible KT-pinned lemma, same idiom as GAP-6) but inflates the green-modulo surface; (A) is
bounded work with no research risk. No recommendation forced here — (A) if the phase has budget,
else (B).

**(b) The Thm 5.5→5.6 push at `d = 3` — what feeds `rigidityMatrix_prop11`'s `hgen`, and what
cannot yet.** KT's Thm 5.6 proof (p. 670) needs Thm 5.5 **at `k = def(G̃)`** (strip a multigraph
to a minimal `k`-dof spanning subgraph) — out of reach of the project's 0-dof-only motive; that
is precisely the adjudicated GAP-6 successor (§1.50(b) option (i), the all-`k` restructure), so
the full Thm 5.6 / the `def > 0` instances of `prop:rigidity-matrix-prop11` are **post-22h by
prior adjudication** (no new estimate change). What IS reachable at 22h-close, and is the honest
"push" deliverable of Leaf 5:

* **The `def = 0`, simple, spanning stratum.** New small theorem (CaseI.lean tail or
  PanelHinge.lean after `rigidityMatrix_prop11`):

```lean
theorem PanelHingeFramework.rankHypothesis_deficiency_of_theorem_55_d3
    [Nonempty α] [Finite α] [Finite β]
    (hfresh : …) (h622 : …)                    -- theorem_55_d3's carries, passed through
    (G : Graph α β) (hG : G.IsMinimalKDof 3 0)
    (hspan : V(G) = Set.univ) (hSimple : G.Simple) :
    ∃ Q : PanelHingeFramework 2 α β, Q.graph = G ∧
      Q.toBodyHinge.RankHypothesis (G.deficiency 3)
```

  Route: the **GP conjunct** of the instance (so Leaf 5 must restate `theorem_55_d3` to conclude
  the full pair `(G.Simple → GP) ∧ bare` instead of projecting `.2` — the bare-only conclusion
  cannot feed `hC`); `hgen` :=
  `finrank_infinitesimalMotions_of_isInfinitesimallyRigidOn_vertexSet` (:431) at `hspan`
  (complement empty → `finrank = D ≤ D + def`, `deficiency_nonneg`); `hC` := GP +
  link-recording + looplessness on edges, **plus an off-edge selector re-aim**: `prop11`'s `hC`
  quantifies over ALL `e : β` and the motive says nothing about non-edge selectors — rebuild
  `Q′ := ⟨G, Q.normal, ends′⟩` with `ends′ := Q.ends` on links and `:= (x₀, y₀)` (two distinct
  bodies, from `2 ≤ |V|`) elsewhere; motions are link-driven so rigidity/GP survive, and
  off-edge extensors are nonzero by GP. (One micro-brick; or alternatively weaken `prop11`'s
  `hC` to `∀ e ∈ E(G)` if the partition cut's usage permits — audit at build time, the cut only
  consumes crossing *edges*.) The consuming site is `rigidityMatrix_prop11` (:1230) itself —
  this is its first genuine `hgen` feed; the landed `rankHypothesis_ofNormals_…` (:2723) remains
  the nested-IH (Claim-6.11) consumer and is not touched. Note `deficiency 3 = 0` here
  (`hG.1`), so the statement's value is its *form* (the Prop-1.1/Thm-5.6 rank-formula shape at
  the stratum Phase 24–26 consume for simple square graphs); the `def > 0` form waits for the
  all-`k` successor.

**(c) The blueprint plan (one docs+TeX commit, after the Lean feeds land).**

1. **Mint the instance node** (panel-layer.tex, after `thm:theorem-55`): a small green node —
   suggest `\label{thm:theorem-55-d3-instance}` — stating the `k = 2` instance of the
   conditioned-motive reduction with `hsplitGP` discharged by the Case-III `d = 3` assembly and
   the explicitly-carried nested-IH hypothesis (GAP-6); `\lean{…theorem_55_d3}` `\leanok`,
   `\uses{thm:minimal-kdof-reduction, lem:theorem-55-base, lem:case-I-realization,
   lem:case-II-realization, lem:case-III, <the GAP-6 red node, item 3>}`. NOT a standalone
   restatement of Thm 5.5 (`thm:theorem-55` itself stays red pending Phase 23 general-`d`,
   §1.41(5)/§1.33(B.2)). While here: `theorem_55_generic` has no `\lean` pin anywhere — add it
   to `thm:theorem-55`'s pin list or the instance node's, builder's choice (checkdecls-gated).
2. **`lem:case-II-realization` / `lem:case-III` flips.** Neither node carries a `\lean` pin
   today, and the discharged producer is the *composition* `case_III_hsplit_producer` +
   `case_III_candidate_dispatch` (no single named decl). Leaf 5 should mint the named wrapper —
   suggest `PanelHingeFramework.case_III_realization`, the `hsplitGP`-shaped composition that
   `theorem_55_d3`'s wiring lambda currently inlines (:6791–:6799) — and pin BOTH nodes to it
   (+ `\leanok`), with prose noting the quantified `h622` carry and `\uses` of the GAP-6 red
   node. This also de-duplicates the wiring lambda.
3. **The GAP-6 carry gets a red node** — suggest `\label{lem:case-III-nested-rank-lower}`
   (case-iii.tex, beside `lem:case-III-seed-rank-upper`): the eq.-(6.22)/(6.1) rank *lower*
   bound at the `k′`-dof `G − v` (`h622`'s exact quantified form, §1.53(f)), no `\lean` pin, a
   one-paragraph statement naming the all-`k` successor as its discharge route. The honesty
   gate for "green-modulo": every `\leanok` node whose Lean signature carries `h622` `\uses`
   this red node (the Phase-21b device-idiom precedent).
4. **`thm:theorem-55` disposition: stays red**; update its proof paragraph to point at the
   instance node for the `d = 3` state of the dichotomy (re-summarize, don't append). If the
   (a2) degenerate route lands, add one honest sentence to the chapter prose: the bare motive
   asserts existence of a possibly-degenerate panel framework (zero support extensors allowed);
   the nonparallel (general-position) conjunct carries the genuine-hinge content.
5. `prop:rigidity-matrix-prop11` stays red until the `def > 0` push (all-`k` successor); the
   (b) stratum theorem can be a small green corollary node under it if minted, else fold into
   the instance node's prose.

**(d) The Leaf-5 cut (supersedes the single "Leaf 5" item; each leaf one commit).**

* **L5a** — the two base/degenerate bricks: `hasFullRankRealization_of_isKDof_zero` ((a2),
  incl. the small `mulTilde`-walk→`G`-connectivity projection if not extractable from :817's
  proof) + `not_simple_of_isMinimalKDof_of_ncard_two` ((a1)). Pure additions. **Gated on the
  user's (a2) sign-off.**
* **L5b** — rewire `theorem_55_d3`: feed `hbase`/`hbaseGP`/`hsplit`/`hcontract` from L5a;
  restate the conclusion to the full pair (drop the `.2` projection, (b)); mint the named
  `case_III_realization` wrapper ((c)2) and route the wiring through it. Statement change →
  grep `blueprint/src` for the decl name per the structural-edit gate (no pin exists yet, so
  no restate due).
* **L5c** — the `hcontractGP` arm, per the user's (a3) scope call: **(A)** c1 Claim 6.6 graph
  side (~2–3 commits) → c2 the Π°-placement producer (signature pin first, then build) → c3
  the dispatch + feed; or **(B)** one commit adding the named `h65` carry to `theorem_55_d3`
  + the feed of the 6.3 arm under the dispatch hypothesis.
* **L5d** — the (b) push stratum: the off-edge selector re-aim micro-brick + 
  `rankHypothesis_deficiency_of_theorem_55_d3`.
* **L5e** — the blueprint commit ((c)1–5).

Phase close = L5a–L5e (≈ 5 commits on route (B), ≈ 9–11 on route (A)), **green-modulo `h622`**
(+ `h65` on route (B)). The two user decisions to obtain before L5a: the (a2) degenerate-route
sign-off and the (a3) (A)-vs-(B) scope call.

### 1.55 The §1.54 adjudications (user, 2026-06-11) + the revised Leaf-5 cut — Decision 1: the bare motive WILL be strengthened to KT's strength, scheduled at the all-`k` redesign (the successor sub-phase "22i", one motive-design moment for both changes); consequence: the (a2) degenerate brick is CUT (carry the three bare slots as named hypotheses instead — zero rework). Decision 2: route (B) (the `h65` carry; the 6.3-vs-6.5 dispatch still lands in 22h)

**(a) Decision 1 — honesty over convenience, scheduled at the single redesign moment.** The
project's formalized statements must match KT's strength: `HasFullRankRealization` gets a
genuine-hinge conjunct. NOT in 22h: the strengthening and the already-adjudicated all-`k`
restructure (§1.50(b) option (i)) reshape the same defs / reduction theorems / bare producers,
so both land in **one successor sub-phase ("22i — the honest all-`k` Theorem 5.5")**, opening
with a single motive design pass (a §1.56-style block) that pins the all-`k` + genuine-hinge
motive together, then: the spine restate, the two KT builds the weak motive skipped (the
graph-level Lemma-5.3 base — the off-link-selector design problem of (a1) — and the Lemma-6.2
non-simple branch, N6a re-aimed), the Lemma-6.5 arm ((a3) steps 1–3), and the `h622`/`h65`/
bare-slot discharges. Postmortem + full rationale: `DESIGN.md` *Statement faithfulness to the
source*; the four process rules extracted from it are in force as of the same date.

**(b) Consequence for the L5 cut — the degenerate brick is cut as pure throwaway.**
`hasFullRankRealization_of_isKDof_zero` would be deleted by the 22i strengthening and briefly
enshrines the vacuous discharge; instead `hbase`/`hsplit`/`hcontract` **stay carried as named
hypotheses on `theorem_55_d3`** (they already ride there since Leaf 4 — zero work now, real
discharges in 22i). `hbaseGP` still discharges via the (a1) vacuity lemma (durable graph
combinatorics, motive-independent). The 22h-close green-modulo surface is therefore the named
family {`h622`, `h65`, `hbase`, `hsplit`, `hcontract`} — each with a tracked artifact (the L5e
red nodes + the 22i obligations), presented in the blueprint as: the GP conjunct is the
delivered content (it is all the `d=3` capstone consumes); the bare conjunct awaits the honest
motive. **At the 22h→22i boundary, seed `notes/Phase22i.md` with a carries table** (carry /
red node / Lean consumption site / discharge sub-plan) — the postmortem's structural fix for
orphaned deferrals.

**(c) The revised cut (supersedes §1.54(d); each leaf one commit).**

* **L5a′ — the blueprint honesty repairs (docs-only).** Per the two new gates: re-prose
  `def:rank-hypothesis` to state the Lean's actual strength (existential over arbitrary
  selector/normals; cheapest witness = the welded framework), naming the KT divergence and the
  22i strengthening obligation (mint the red node `def:genuine-hinge-realization` or
  equivalent for the honest form); restate `lem:case-I-realization`'s prose to carry
  `hcSimple` as the KT-6.3 case hypothesis and mint the red node for the 6.5 arm
  (`lem:case-I-dispatch`, statement = the (a3) dispatch + Lemma-6.5 decomposition). No Lean.
* **L5b′ — `not_simple_of_isMinimalKDof_of_ncard_two` ((a1)) + the `theorem_55_d3` re-shape:**
  feed `hbaseGP` (the vacuity absurd); keep `hbase`/`hsplit`/`hcontract` as hypotheses;
  restate the conclusion to the full `(Simple → GP) ∧ bare` pair (drop the `.2` projection,
  (b)); mint the named `case_III_realization` wrapper ((c)2). Statement change → grep
  `blueprint/src` per the structural-edit gate.
* **L5c′ — the `hcontractGP` dispatch (route (B)):** `by_cases` on the simple-contraction
  existence; positive → the 6.3-arm adaptor ((a3) exact wiring); negative → the named carry
  `h65` (the 6.5-stratum `hcontractGP` instance, quantified per the (a3) step-3 negative
  branch — every proper rigid subgraph has non-simple contraction — in the `h622` carry
  idiom). One commit.
* **L5d′ — unchanged** (§1.54(d) L5d: the off-edge selector re-aim micro-brick +
  `rankHypothesis_deficiency_of_theorem_55_d3`).
* **L5e′ — the blueprint close commit** ((c)1–5, adjusted: the instance node presents the
  carried bare family per (b); the L5a′ red nodes enter the carries roster).

Phase close = L5a′–L5e′ (≈ 5 commits), green-modulo the named family of (b). Then open 22i
with the motive design pass.

### 1.56 The 22i motive design pass — the all-`k` + genuine-hinge motive pinned together: the honest bare motive moves to the free-hinge `BodyHingeFramework` carrier (a panel assignment + extensor-in-panel containment + the ℤ-cast rank-deficiency equality), the generic motive keeps its `PanelHingeFramework` carrier with only the rank form generalized, and the induction becomes KT's four-case all-`k` `|V|`-recursion (Lemma 6.1 not-2-edge-connected + Lemma 6.8 `k>0` split are NEW cases the 0-dof reduction never had) (2026-06-11)

> **Docs-only design pass (the 22i phase-open motive pin; §1.55(a)'s "single motive design
> moment").** Lean read this pass (declarations, current line numbers): PanelHinge.lean —
> `PanelHingeFramework` (:65 — `normal : α → Fin (k+2) → ℝ`, `ends : β → α × α`; the hinge IS
> the derived meet), `toBodyHinge` (:87, `supportExtensor e = panelSupportExtensor (normal
> (ends e).1) (normal (ends e).2)`), `toBodyHinge_supportExtensor_ne_zero_iff` (:105 — nonzero
> ⟺ the two selected normals LI), `IsHingeCoplanar` (:920 — "arises as a `toBodyHinge`", so it
> inherits the same hinge-as-meet expressiveness limit), `HasFullRankRealization` (:979),
> `HasGenericFullRankRealization` (:1033), `hasFullRankRealization_of_generic` (:1046),
> `theorem_55` (:1098), `theorem_55_generic` (:1146), `rigidityMatrix_prop11` (:1230 — `hgen`
> ℤ-cast, the established mixed-`ℤ` precedent); ForestSurgery.lean — `minimal_kdof_reduction`
> (:1198) and `minimal_kdof_reduction_full` (:1266), both **`IsMinimalKDof n 0`-only** in every
> branch hypothesis and the conclusion, `splitOff_isMinimalKDof` (0-dof → 0-dof only),
> `splitOff_removeVertex_minimalKDof` (:2035 — note `IsMinimalKDof n (deficiency)` with the
> dof ℤ-valued and `0 ≤ def ≤ D − 2`); ReducibleVertex.lean — `exists_degree_eq_two` (:588,
> KT 4.6 — its degree-≥2 half routes through `two_le_crossingEdges_of_isKDof_zero`, i.e. the
> **0-dof** 2-edge-connectivity, so the all-`k` form must take 2-edge-connectivity as a *case
> hypothesis*), `simple_of_isMinimalKDof_of_noRigid` (:625 — G0, no 2-edge-connectivity
> needed); Contraction.lean — `rigidContract_isMinimalKDof` (:696, the N4 bridge, **0-dof →
> 0-dof**; KT 3.5 is all-`k`); CaseI.lean — `case_III_realization` (:6750, the `h622`
> consumption), `theorem_55_d3` (:6799, the five carries :6802–:6839),
> `rankHypothesis_deficiency_of_theorem_55_d3` (:6903); GenericityDevice.lean —
> `hasFullRankRealization_of_splice_of_supportExtensor` (:822, N6a) +
> `finrank_span_rigidityRows_of_rigidOn` (W2). KT 2011 read **against the PDF this pass**:
> p. 669 (Lemma 5.2 + the §5.2 opening; Lemma 5.3 statement), p. 670 (Lemma 5.3 proof — the
> realization has Π(u) = Π(v) and p(e) ≠ p(f); Theorem 5.5 + 5.6 statements + 5.6's proof:
> strip to a minimal `k`-dof spanning subgraph, Thm 5.5, projective move, re-add edges),
> p. 671 (the base trichotomy (i) `E = ∅` / (ii) one edge / (iii) the parallel pair via
> Lemma 3.2, "(i) and (ii) are trivial"; **the four-case `|V| ≥ 3` split**; the induction
> hypothesis (6.1) quantified over *every* nonnegative `k_H`), p. 672 (Lemma 6.1 — the
> cut-edge decomposition, `k = k₁ + k₂ + 1` by Lemma 3.6, sides minimal `kᵢ`-dof by Lemma
> 3.3, the block-triangular rank addition over the cut row), pp. 673–674 (the §6.2 trifurcation
> prose; Lemma 6.2 — `G[{e,f}]` is a proper rigid subgraph, Lemma-5.3 leg with **coincident
> panels** `Π(a) = Π(b) = Π(v*)`, eq. (6.2)–(6.5) rank addition; Lemma 6.3 statement),
> p. 677 (Lemma 6.7 — (i) the `|V|=3` triangle, (ii) `G_v^{ab}` simple at `|V| ≥ 4`; "G is
> simple since multiple edges induce a proper rigid subgraph"), pp. 677–679 (Lemma 6.8 — the
> `k > 0` split: `G_v^{ab}` minimal `(k−1)`-dof by **Lemma 4.8**, the eq. (6.12) placement,
> eqs. (6.13)–(6.17) column ops, rank ≥ (D−1) + D(|V∖v|−1) − (k−1) = D(|V|−1) − k, then
> Lemma 5.2 to nonparallel). No `.lean`/`.tex` edits this pass.

**(a) The expressiveness finding that forces a carrier split.** KT's panel-hinge realization
assigns each vertex a hyperplane *panel* and each edge `uv` a **freely chosen** `(d−2)`-flat
hinge `p(uv) ⊆ Π(u) ∩ Π(v)`. The project's `PanelHingeFramework` *derives* the hinge as the
meet of the two selected normals — strictly less expressive exactly when two adjacent panels
**coincide**: the meet degenerates (`panelSupportExtensor n n = 0`) where KT picks an arbitrary
`(d−2)`-flat inside the common panel. The coincident-panel freedom is load-bearing in exactly
the two non-simple KT builds the weak motive skipped: **Lemma 5.3** (p. 670: the parallel-pair
base is realized with `Π(u) = Π(v)` and two *distinct* genuine hinges `p(e) ≠ p(f)` in that
common panel — under a link-recording selector with derived hinges, the two extensors are
forced *equal*, so the two row blocks span only `D − 1 < D` and the honest rank is
unreachable; quantifier-level check, no Lean needed) and **Lemma 6.2** (pp. 673–674: the
contraction splice takes `Π(a) = Π(b) = Π(v*)`). Verdict: **the honest bare motive cannot
keep the `PanelHingeFramework` carrier.** It moves to the free-hinge `BodyHingeFramework`
(KT's actual model) plus an explicit panel assignment with a containment condition — while
the **generic (simple-case) motive keeps its `PanelHingeFramework` carrier unchanged**: for a
simple `G` in general position every two adjacent panels are transversal, so the hinge *is*
the meet and nothing is lost — and every landed GP producer (the entire 22a–22h spine)
survives untouched-but-for the rank form of (c).

**(b) The pinned motives (M1–M5).** Names indicative, checkdecls-gated at L0; the `(k, n)`
parameter pair stays as in `theorem_55_generic` (grading `k`, multiplicity `n`; the consumers
relate them, `screwDim k = bodyBarDim n` at the instance).

* **M1 — the containment predicate** (new, PanelLayer.lean or RigidityMatrix.lean):

  ```lean
  /-- The k-extensor `C` lies in the panel with normal `n`: it is spanned by points of the
  hyperplane `n^⊥`. -/
  def ExtensorInPanel (C : ScrewSpace k) (n : Fin (k + 2) → ℝ) : Prop :=
    ∃ p : Fin k → (Fin (k + 2) → ℝ), C = Matrix.extensor p ∧ ∀ i, p i ⬝ᵥ n = 0
  ```

  **V1 (resolve at the L0 pin):** the exact formulation — the pointwise form above vs the
  annihilator/`annihRow` dual form vs "in the image of `meet` with `n`" — chosen against what
  the two consumers need: the Lemma-5.3/6.2 *constructions* (want pointwise: exhibit the
  points) and the Thm-5.6 re-add step (wants "any `(d−2)`-flat in a panel intersection"). The
  landed homogeneous-incidence machinery (`exists_homogeneousIncidence_of_normals`,
  RigidityMatrix.lean:455; `omitTwoExtensor`) is the existing API to align with. The forgetful
  map (M4) needs: the meet `panelSupportExtensor n₁ n₂` of LI normals satisfies
  `ExtensorInPanel · n₁ ∧ ExtensorInPanel · n₂` — expected derivable from the same machinery.

* **M2 — the honest bare motive** (replaces `HasFullRankRealization`; the
  `def:genuine-hinge-realization` form):

  ```lean
  def HasPanelRealization (k n : ℕ) (G : Graph α β) : Prop :=
    ∃ (F : BodyHingeFramework k α β) (normal : α → Fin (k + 2) → ℝ),
      F.graph = G ∧
      (∀ v ∈ V(G), normal v ≠ 0) ∧
      (∀ e u v, G.IsLink e u v → F.supportExtensor e ≠ 0 ∧
        ExtensorInPanel (F.supportExtensor e) (normal u) ∧
        ExtensorInPanel (F.supportExtensor e) (normal v)) ∧
      (Module.finrank ℝ (Submodule.span ℝ F.rigidityRows) : ℤ)
        = screwDim k * ((V(G).ncard : ℤ) - 1) - G.deficiency n
  ```

  Design notes, each deliberate: **(i)** the carrier is the bare `BodyHingeFramework` — all
  Phase-18 rank machinery applies verbatim, and no `ends` selector exists (the containment is
  quantified relationally over links, so no link-recording conjunct is needed or possible);
  **(ii)** genuine hinges (`≠ 0`) and containment are required **on links only** and panels
  nonzero **on `V(G)` only** (the `V(G)`-relative discipline — ambient junk bodies and
  off-edge labels unconstrained, same reason as Phase 21b's motive re-plan); **(iii)** the
  rank conjunct is the **ℤ-cast equality** at the graph's own deficiency (`G.deficiency n` is
  already ℤ; the `rigidityMatrix_prop11` `hgen` precedent) — no separate dof parameter, the
  graph carries its dof, and `IsMinimalKDof n k` hypotheses at use sites pin `deficiency = k`;
  **(iv)** the *equality* (not `≥`) is KT-faithful; producers prove `≥` and close with **B2**
  (below). At `|V| = 1` the convention is harmless (`def = 0`, target `0`).

* **M3 — the generic motive restate** (in place, same name `HasGenericFullRankRealization`,
  same `PanelHingeFramework` carrier): the conclusion conjunct
  `Q.toBodyHinge.IsInfinitesimallyRigidOn V(G)` is replaced by the same ℤ-cast rank equality
  as M2 (now gaining the `n` parameter); `IsGeneralPosition`, link-recording, and the
  `AlgebraicIndependent ℚ` conjuncts are unchanged. At `def = 0` the two forms are equivalent
  (**B1**); the landed producers restate through B1, not by re-proof.

* **M4 — the conditioned pair + forgetful map.** The induction motive stays the pair
  `Pc G := (G.Simple → HasGenericFullRankRealization k n G) ∧ HasPanelRealization k n G`
  (KT p. 670: "(nonparallel, if `G` is simple)"). The forgetful map
  `hasPanelRealization_of_generic [G.Loopless] : Generic → Bare` is no longer projection-
  trivial: take `F := Q.toBodyHinge`, `normal := Q.normal`; genuine hinges on links = GP +
  link-recording + `hle.ne` (loopless); containment = the M1 meet-decomposition lemma; panel
  nonzeroness = pairwise LI at a second body (`2 ≤ |V(G)|` ambient). One lemma, bounded.

* **M5 — naming/migration.** `HasFullRankRealization` is **deleted** (Decision 1, §1.55(a):
  no weak form survives to be cited); `HasPanelRealization` is the new honest bare motive;
  `HasGenericFullRankRealization` restates **in place**. Blueprint: `def:genuine-hinge-
  realization` gains the `\lean{…HasPanelRealization}` pin + `\leanok` at L0;
  `def:rank-hypothesis` re-proses to the *rank-form* substrate both motives share (it keeps
  `IsInfinitesimallyRigidOn`/`RankHypothesis` pins — those predicates remain the `def = 0`
  bridge targets); every `lem:`/`thm:` node naming the old motive restates per slice
  (structural-edit gate: grep `blueprint/src` per statement-changing commit).

**(c) The all-`k` reduction principle (the Phase-20 generalization).** KT p. 671: induction
on `|V|` with IH (6.1) over **every** dof; base `|V| = 2` is the Lemma-3.2 trichotomy; at
`|V| ≥ 3` a **four-case** split. The 0-dof `minimal_kdof_reduction[_full]` stays (it drives
`thm:minimal-kdof-reduction`, untouched); a NEW principle lands beside it:

```lean
theorem minimal_kdof_reduction_all_k [DecidableEq β] [Finite α] {n : ℕ}
    {P : Graph α β → Prop}
    (hbase : ∀ (k : ℤ) (G : Graph α β), G.IsMinimalKDof n k → V(G).ncard ≤ 2 → P G)
    (hcut : ∀ (k : ℤ) (G : Graph α β), G.IsMinimalKDof n k → 3 ≤ V(G).ncard →
      ¬ G.TwoEdgeConnected → IH → P G)
    (hcontract : ∀ (k : ℤ) (G : Graph α β), G.IsMinimalKDof n k → 3 ≤ V(G).ncard →
      (∃ H, H.IsProperRigidSubgraph G n) → IH → P G)
    (hsplitPos : ∀ (k : ℤ) (G : Graph α β), G.IsMinimalKDof n k → 0 < k →
      3 ≤ V(G).ncard → G.TwoEdgeConnected → (∀ H, ¬ H.IsProperRigidSubgraph G n) →
      IH → P G)
    (hsplitZero : ∀ G : Graph α β, G.IsMinimalKDof n 0 → 3 ≤ V(G).ncard →
      G.TwoEdgeConnected → (∀ H, ¬ H.IsProperRigidSubgraph G n) → IH → P G) :
    ∀ (k : ℤ) (G : Graph α β), G.IsMinimalKDof n k → P G
  -- IH abbreviates: ∀ (k' : ℤ) (G' : Graph α β), G'.IsMinimalKDof n k' →
  --   V(G').ncard < V(G).ncard → P G'
```

Design notes: **(i)** the vertex floor drops to nothing (base covers `ncard ≤ 2`): KT's
Lemma-6.1 decomposition produces cut-sides of size 1, which its IH application silently
covers — the formalization makes the `ncard ≤ 1` case explicit (a realization with no
constrained links; `def = 0` there) rather than excluding it. **(ii)** `k : ℤ` with
nonnegativity carried inside `IsMinimalKDof` facts (`deficiency_nonneg`), matching the landed
ℤ-valued deficiency. **(iii)** `G.TwoEdgeConnected` is a NEW predicate (**V2**, pin at the L1
design pass): the candidate form is the crossing-edge count `∀ V' ⊂ V(G), V'.Nonempty →
V' ≠ V(G) → 2 ≤ (crossing edges of V')` over the landed `crossingEdges` machinery —
*including* connectivity (KT's 2-edge-connected is connected + bridgeless; the disconnected
arm of Lemma 6.1 routes through the same `hcut` case). **(iv)** the dichotomy driver inside
the proof: at `3 ≤ ncard`, classical cases on 2EC, then on rigid-subgraph existence, then on
`k = 0` (`deficiency` decidable enough via `by_cases` on the ℤ equality); `hsplitPos`'s
degree-2 vertex is found *inside the producer* (the (β)-interface precedent — hand the full
IH, let the producer choose its split), so the principle itself needs **no** new
combinatorial lemma beyond the case split. The combinatorial bricks live in the *producers*:

* **landed and reusable as-is:** G0 `simple_of_isMinimalKDof_of_noRigid` (no-rigid ⟹ simple,
  no 2EC needed); `splitOff_removeVertex_minimalKDof` (the `k' ≤ D − 2` shell);
  `splitOff_isMinimalKDof` (the `k = 0` split step).
* **restate/generalize:** `exists_degree_eq_two` — the all-`k` form takes `G.TwoEdgeConnected`
  as a hypothesis in place of the 0-dof-derived cut bound (**V3**: confirm the average-degree
  half `exists_degree_le_two` is already dof-agnostic; expected yes, it is a count);
  `rigidContract_isMinimalKDof` — KT 3.5 is all-`k`; the N4 proof routes through def=corank
  on the contraction, generalization expected mechanical (**V4**).
* **NEW bricks:** the `|V| ≤ 2` trichotomy (KT Lemma 3.2 consequence: at `ncard = 2`
  minimality bounds the parallel class at 2, so `E ∈ {∅, {e}, {e,f}}` with `k ∈ {D, 1, 0}`
  respectively); the cut-edge decomposition (KT Lemma 3.6 `k = k₁ + k₂ + 1` + Lemma 3.3
  sides-minimal — wholly new `M(G̃)` matroid work, the `hcut` producer's substrate); KT
  Lemma 4.8 (at `k > 0`, no rigid subgraph: `G_v^{ab}` is minimal `(k−1)`-dof — the dof
  *decrements*, unlike the landed 4.7).

**(d) The case-producer map (what discharges each branch of (c) at the conditioned pair).**

* **`hbase`** — `ncard ≤ 1`: free. `ncard = 2` trichotomy: (i) `E = ∅` (`k = D`): rank 0,
  any nonzero panel normals — free; (ii) one edge (`k = 1`): two LI normals, hinge = meet,
  rank `D − 1` (the landed single-row rank fact); GP conjunct = the same witness; (iii) the
  parallel pair (`k = 0`): **the graph-level Lemma 5.3, the genuinely new geometric brick** —
  equal normals `n` at `u, v`, two non-proportional extensors `C_e, C_f` built from explicit
  point tuples inside `n^⊥` (M1's pointwise form), rank `D` via the two-row-block computation;
  re-aim Pinning.lean's framework-level `theorem_55_base` (:630 — its LI-extensor-pair
  hypothesis is exactly `![C_e, C_f]` LI) as the rank engine. GP conjunct vacuous
  (`not_simple_of_isMinimalKDof_of_ncard_two`, landed L5b′).
* **`hcut`** — KT Lemma 6.1 (NEW, p. 672): decompose at the cut (Lemma-3.6 brick), realize the
  sides by IH, combine: side hinges unchanged, the cut edge's hinge = a flat in
  `Π(u) ∩ Π(v)`; rank addition is the landed block-triangular pattern (Lemma 5.1 / the
  pinned-block suite) over the `D − 1` cut rows. KT takes an isometry to make the two sides'
  panels transversal; **the project's fixed-ambient-seed style does better** — both sides
  realized at one global alg-indep seed make cross-side transversality automatic for the GP
  conjunct, and for the bare conjunct transversality at the cut pair is not even needed
  (any flat inside a *common* panel still has `C ≠ 0` — the free-hinge carrier absorbs it).
  Verify the route at the L4 pin (**V5**).
* **`hcontract`** — dispatch on `G.Simple`: simple → the landed 6.3/6.5 GP arm (restated per
  (e)) + forgetful M4; non-simple → **KT Lemma 6.2 (NEW, the N6a re-aim)**: `G' := G[{e,f}]`
  (a parallel pair, proper rigid — the landed G0-adjacent brick), the Lemma-5.3 leg *at the
  contraction's panel* (`Π(a) = Π(b) = Π(v*)`, the coincident-panel freedom again), IH at
  `G/E'` (bare honest), eq. (6.3)–(6.5) rank addition. The old N6a
  `hasFullRankRealization_of_splice_of_supportExtensor` (GenericityDevice:822) is the
  closest landed splice — **V6**: read its exact statement at the L5 pin and re-aim at the
  honest carrier (its `hends`/`hsupp` shape was built for the weak motive).
* **`hsplitPos`** — KT Lemma 6.8 (NEW assembly, mostly landed parts): degree-2 vertex
  (restated 4.6), `G_v^{ab}` minimal `(k−1)`-dof (NEW Lemma 4.8) and simple (landed 6.7(ii)
  analog = R3/`splitOff` simplicity at `|V| ≥ 4`; the `|V| = 3` triangle is 6.7(i) = the
  landed T1–T4), IH at `G_v^{ab}`, the eq. (6.12) placement — **the landed 22c stratum-1
  brick `case_II_placement_eq612` is exactly eqs. (6.13)–(6.17)** — giving rank
  `≥ (D−1) + D(|V∖v|−1) − (k−1) = D(|V|−1) − k`, then the GP conjunct via the Lemma-5.2
  shear transfer (**V7**: how much of the 22h W-suite — the one-parameter rank transfer
  W3/W6f and the certify-then-rebase pattern — re-instantiates here; expected substantial,
  it was built for the *harder* `k = 0` case).
* **`hsplitZero`** — the landed 22h Case-III producer, restated: `case_III_realization`'s
  carried `h622` hypothesis is **replaced by a derivation from the all-`k` IH** (the
  `lem:case-III-nested-rank-lower` discharge): IH at `G_v = G − v` (simple, minimal
  `k'`-dof, `k' ≤ D − 2` by the landed shell, smaller) gives a generic realization at rank
  `D(m−1) − k'` at its own seed; extract the rational rank-polynomial witness (**V8**: the
  landed subfamily-extraction `exists_independent_panelRow_subfamily_of_rigidOn` is
  rigid-framework-shaped — generalize to the rank form, bounded); transfer to the given
  `(ends, q)` by the landed footnote-6 bridge (`lem:case-III-seed-rank-bridge` /
  `finrank_…_le_of_rankPolynomial_algebraicIndependent`, no `hspan`). The bare conjunct of
  this branch is **free**: G0 gives `G.Simple`, so forgetful ∘ (the GP conclusion) — this is
  the `hsplit` carry's entire discharge.

**(e) The spine, the instance, and the Thm-5.6 push.** `theorem_55_generic` → the all-`k`
conditioned spine over (c) (name: `theorem_55_all_k`); `theorem_55` (bare, 0-dof) is
**superseded and deleted** with `thm:theorem-55` re-pinned (it finally goes green at `d = 3`
content-wise; it stays red only for general-`d`, Phase 23 — restate its red-rationale prose
then). `theorem_55_d3` restates with **zero carried hypotheses** (`hfresh` stays: ambient
data). The 6.5 arm (`h65` discharge) is the unchanged §1.54(a3) plan — Claim 6.6 graph side
+ the Π°-placement producer (its own §1.53-style pin before build) + the landed L5c′
dispatch; note Claim 6.6's conclusion lands *in* the `k = 0` stratum (KT p. 676: maximality
forces `G = G″` rigid), so the arm needs no all-`k` generality. Then **Theorem 5.6 at
`d = 3`** (the `def > 0` `prop:rigidity-matrix-prop11` feed, KT p. 670): strip `G` to a
deficiency-preserving minimal `k`-dof spanning subgraph (NEW combinatorial brick — greedy
edge deletion under `def` invariance), apply the instance, re-add edges
(`lem:motions-mono-of-graph-le`, landed) with hinges in the panel intersections — KT's
projective move is expected **free** in the project's homogeneous model (two distinct linear
hyperplanes always meet in a `(d−2)`-subspace; **V9** verify, and the coincident-panel
re-add is absorbed by the free-hinge carrier). `rankHypothesis_deficiency_of_theorem_55_d3`
survives as the `def = 0` stratum instance. Corollary 5.7 stays **Phase 26** (it needs the
Phase-24 3-D matroid + Phase-25 molecule equivalence); 22i's deliverable boundary is
KT-strength Thm 5.5 + 5.6 at `d = 3`.

**(f) Bridges (L0).** **B1**: at `def = 0` + `V(G).Nonempty`, the ℤ-cast rank equality ⟺
`IsInfinitesimallyRigidOn V(G)` — assemble from the landed W2
(`finrank_span_rigidityRows_of_rigidOn`, rigid → count) and the relative-count adapter
(`lem:isInfRigidOn-of-relative-count` direction, count → rigid). **B2**: the universal
`V(G)`-relative upper bound `(finrank span rigidityRows : ℤ) ≤ D(|V(G)|−1) − def(G̃)` *given
genuine hinges on links* — the `V(G)`-relative form of the landed hub bound
(`screwDim_add_deficiency_le_finrank_infinitesimalMotions` is absolute + all-`e`-quantified;
re-derive relatively or via the `reaim` idiom; **V10**). B2 is what lets every producer prove
`≥` and conclude the M2/M3 equality.

**(g) Verification items** (resolve each at its layer's design pass, before that layer's
first Lean commit): **V1** `ExtensorInPanel`'s exact form; **V2** the `TwoEdgeConnected`
predicate; **V3** `exists_degree_le_two` dof-agnosticity; **V4** `rigidContract_isMinimalKDof`
all-`k` generalization shape; **V5** the Lemma-6.1 fixed-seed transversality route; **V6**
N6a's statement vs the honest carrier; **V7** the W-suite reuse at `k > 0`; **V8** the
subfamily extraction at rank (non-rigid) form; **V9** the homogeneous projective-move
freeness; **V10** the relative hub bound B2.

**(h) The layer plan** (the 22i to-do skeleton; each L-layer opens with its own §1.57+
signature pin — the carries table + checklist live in `notes/Phase22i.md`, which points
here): **L0** motives M1–M5 + bridges B1/B2 + the def-node blueprint flips; **L1** the
combinatorial bricks ((c)'s census: trichotomy, 3.6/3.3-cut, 3.5-all-`k`, 4.6-restate, 4.8);
**L2** `minimal_kdof_reduction_all_k`; **L3** the base producer (incl. the Lemma-5.3
coincident-panel brick); **L4** Lemma 6.1; **L5** Lemma 6.2 + the 6.3/6.5 all-`k` restate of
`case_I_realization`; **L6** Lemma 6.8 (`k > 0` split); **L7** the Case-III rewire (`h622`
discharge); **L8** the 6.5 arm (`h65` discharge; §1.54(a3)); **L9** the spine + instance
restate (all carries gone) + blueprint close; **L10** Thm 5.6 at `d = 3` (the `def > 0`
prop11 feed). Structural-edit mode throughout (no new blueprint chapter; per-slice restates
across panel-layer/case-i/case-iii/the base section). Estimate: ~20–30 commits — plural
sessions; the layer plan is the tracking artifact.

### 1.57 The L0 signature pin — V1 resolved (pointwise `ExtensorInPanel`, with the coercion fix; the meet-decomposition lemma pinned at `k = 2` over the landed PanelLayer duality), V10 resolved (B2 = relative re-derivation via a complement-separating partition refinement; `reaim` NOT applicable — the partition bricks never needed all-`e` `hC` in the first place), the exact M1–M5/B1/B2 statements, and the L0a–L0e slice cut (2026-06-11)

> **Docs-only design pass (the L0 pin).** Lean read this pass beyond §1.56's census:
> RigidityMatrix.lean — `ScrewSpace` (:86, `↥(⋀[ℝ]^k (Fin (k+2) → ℝ))` — a *bundled
> submodule element*, the coercion finding in (a)), `exists_ne_zero_dotProduct_eq_zero`
> (:181, general-`d`!), `exists_independent_perp_pair` (:381),
> `exists_homogeneousIncidence_of_normals` (:455, the `mulVecLin` rank-nullity pattern),
> `BodyHingeFramework` (:670 — `graph` + `supportExtensor : β → ScrewSpace k`, **no `ends`
> field**, confirming M2's relational containment), `rigidityRows` (:905),
> `IsInfinitesimallyRigidOn` (:2436); Extensor.lean — `extensor` (:194, lands in the **full**
> `ExteriorAlgebra ℝ (Fin (d+1) → ℝ)`, not the graded piece); PanelLayer.lean —
> `panelSupportExtensor` (:231), `panelSupportExtensor_eq_complementIso_extensor` (:330),
> `panelSupportExtensor_join_eq_zero_of_eq_zero` (:356, **the meet-lemma engine**),
> `normalsJoin_ne_zero_iff` (via :243), `partitionConstant`/`finrank_partitionConstant`
> (:1152/:1192 — **exact** `D·|range f|`, the V10 key), `mul_numParts_le_finrank_partitionConstant`
> (:1211 — the `≤` is *only* the `f''V(G) ⊆ range f` slack), `partitionMotions` (:1224),
> `finrank_partitionCutMap_codomain` (:1369 — `hC` quantified **over crossing edges only**),
> `screwDim_mul_numParts_sub_le_finrank_partitionMotions` (:1406),
> `screwDim_add_deficiency_le_finrank_infinitesimalMotions` (:1464, the hub bound + its
> `hDcast` reconciliation `bodyBarDim (k+1) = screwDim k`); Pinning.lean — `RankHypothesis`
> (:592), `theorem_55_base` (:630), `isInfinitesimallyRigidOn_vertexSet_of_finrank_le`
> (:1369, N3); GenericityDevice.lean —
> `finrank_infinitesimalMotions_of_isInfinitesimallyRigidOn_vertexSet` (:431),
> `finrank_span_rigidityRows_of_rigidOn` (:466, W2 — its inline coannihilator-complement
> count is the brick B1/B2 share), `hasFullRankRealization_of_splice_of_supportExtensor`
> (:822, N6a); PanelHinge.lean — the motives (:979/:1033), `hasFullRankRealization_of_generic`
> (:1046 — **no live consumers**, doc-comment references only), `theorem_55` (:1098),
> `theorem_55_generic` (:1146), `rigidityMatrix_prop11` (:1230); CaseI.lean — the conditioned
> IH's bare `.2` conjunct is **never destructured on the live route** (all live IH uses are
> `.1`: :2147, :2172, :5329 — §1.54(a2)'s vacuity finding at the consumption level), `reaim`
> (:6871), `theorem_55_d3` (:6799), `rankHypothesis_deficiency_of_theorem_55_d3` (:6903);
> Framework.lean — `bodyBarDim` (:61, `n(n+1)/2`); blueprint panel-layer.tex —
> `def:rank-hypothesis` (:149), `def:genuine-hinge-realization` (:198),
> `thm:theorem-55` (:216), `thm:theorem-55-d3-instance` (:275). No `.lean`/`.tex` edits this
> pass.

**(a) V1 resolved: the pointwise form, with two fixes to §1.56's sketch.** Verdict —
**pointwise points-in-hyperplane**, against the three candidates:

* *Pointwise wins on the consumer audit.* The Lemma-5.3/6.2 constructions (L3/L5) *exhibit*
  explicit point tuples inside the common panel — pointwise is their native output. The
  Thm-5.6 re-add step (L10) consumes an existential ("some `(d−2)`-flat in the
  intersection") — an `∃ p` form is exactly what it opens. The homogeneous-incidence
  machinery (`exists_homogeneousIncidence_of_normals`, `exists_ne_zero_dotProduct_eq_zero` —
  the latter already general-`d`) produces points-with-`⬝ᵥ = 0` data, aligning with
  pointwise verbatim. The annihilator-dual and meet-image forms both route through
  `exteriorPower.map`-range plumbing whose injectivity/range API is landed only at `⋀²ℝ⁴`
  (Meet.lean N3b-1/2) — they'd make the *general-`k` definition* depend on `d = 3`-only
  machinery, exactly backwards.
* *Fix 1 (the coercion).* §1.56's sketch `C = Matrix.extensor p` is type-incorrect twice
  over: the project's `extensor` (Molecular namespace, not `Matrix`) lands in the **full**
  `ExteriorAlgebra ℝ (Fin (k+2) → ℝ)`, while `C : ScrewSpace k` is the bundled graded
  piece. The equality is stated through the submodule coercion.
* *Fix 2 (placement).* `RigidityMatrix.lean` (graph-free geometry section, beside the
  homogeneous-incidence suite), **not** PanelLayer: the def needs only `extensor` +
  `ScrewSpace` + `⬝ᵥ`, all in scope there; the meet-decomposition *lemma* (below) needs the
  PanelLayer duality and lives there.

```lean
-- RigidityMatrix.lean (graph-free geometry section, after the incidence suite)
/-- The k-extensor `C` lies in the panel with normal `n`: it is the extensor of `k`
points of the hyperplane `n^⊥`. -/
def ExtensorInPanel {k : ℕ} (C : ScrewSpace k) (n : Fin (k + 2) → ℝ) : Prop :=
  ∃ p : Fin k → Fin (k + 2) → ℝ,
    (C : ExteriorAlgebra ℝ (Fin (k + 2) → ℝ)) = extensor p ∧ ∀ i, p i ⬝ᵥ n = 0
```

Notes: `C = 0` satisfies the predicate (a degenerate `p`) — nonzero-ness is M2's separate
conjunct, deliberately. Scalars absorb into a point for `k ≥ 1` (`c • extensor p =
extensor (update p 0 (c • p 0))`); the `k = 0` degeneracy (`extensor ![] = 1`) is
irrelevant to every consumer (`k = 2` producers, `k ≥ 1` motives in practice) and left as
is.

**The meet-decomposition lemma (M4's engine) — pinned at `k = 2`, PanelLayer.lean:**

```lean
/-- The meet of two transversal panels is the extensor of two points of both panels. -/
theorem exists_extensor_eq_panelSupportExtensor {n₁ n₂ : Fin 4 → ℝ}
    (h : LinearIndependent ℝ ![n₁, n₂]) :
    ∃ p : Fin 2 → Fin 4 → ℝ,
      ((panelSupportExtensor (k := 2) n₁ n₂ : ScrewSpace 2) :
        ExteriorAlgebra ℝ (Fin 4 → ℝ)) = extensor p ∧
      ∀ i, p i ⬝ᵥ n₁ = 0 ∧ p i ⬝ᵥ n₂ = 0
```

(+ the one-line corollary packaging it as `ExtensorInPanel … n₁ ∧ ExtensorInPanel … n₂`.)
Proof route, all landed API: (1) two **linearly independent** common-perp points `p₀, p₁`
of `{n₁, n₂}` — the `mulVecLin` rank-nullity pattern of
`exists_homogeneousIncidence_of_normals` (ker of the 2-row pairing map has finrank ≥ 2;
extract an independent pair); (2) every `r : Dual (ScrewSpace 2)` killing the meet kills
`extensor ![p₀, p₁]` — **verbatim `panelSupportExtensor_join_eq_zero_of_eq_zero`**; (3) the
finite-dimensional double-annihilator step (`(∀ r, r C = 0 → r x = 0) → x ∈ span {C}` —
the one mathlib-search item of the slice; if no exact match, a small dual-separation mirror
brick); (4) `extensor ![p₀, p₁] ≠ 0` from independence via `normalsJoin_ne_zero_iff` +
`normalsJoin_coe`, so the proportionality scalar is nonzero and rescales into `p₀`.
**Why `k = 2` and not general `k`:** every consumer of M4 is a `d = 3` producer
(`theorem_55_d3`'s wiring; the GP spine is `ScrewSpace 2`-hardcoded), and step (2)'s engine
is the `Fin 4` duality suite; the general-`k` meet-in-`⋀^k(n^⊥)` half is genuinely new
exterior-algebra work that belongs to Phase 23 (general `d`), not here. The general-`k`
*definition* costs nothing; only the meet lemma is `d = 3`.

**(b) V10 resolved: B2 is a relative re-derivation; `reaim` is not applicable — and not
needed.** Two findings against the landed proofs:

* *The all-`e` quantification of the hub bound's `hC` is an artifact, not a real
  obstruction.* `finrank_partitionCutMap_codomain` consumes `hC` only **on crossing edges**
  (`∀ e ∈ crossingEdges f, …`), and crossing edges are links by definition
  (`crossingEdges = {e ∈ E(G) | ∃ x y, IsLink e x y ∧ …}`). The hub bound merely *passes*
  its all-`e` `hC` down (`fun e _ => hC e`). So the relative siblings take the M2-shaped
  per-link hypothesis `∀ e u v, IsLink e u v → supportExtensor e ≠ 0` directly — no `reaim`
  re-aim of off-link selectors is needed anywhere in the B2 chain. (`reaim` solved a
  different problem: feeding `rigidityMatrix_prop11`'s genuinely all-`e` `hC`, which keeps
  its shape; the L10 instance keeps using it there.)
* *The genuine gap is the ambient complement count.* The landed hub bound gives
  `D + def ≤ dim Z`; combined with the coannihilator complement
  (`finrank span rows + dim Z = D|α|`, W2's inline count) it yields only
  `finrank span rows ≤ D(|V(G)|−1) − def + D·|V(G)ᶜ.ncard|` — too weak by the ambient junk
  bodies whenever `G` does not span `α`. The fix is to make the deficiency-attaining
  partition **also separate every body of `V(G)ᶜ` into its own part**: each junk body
  carries no link (links' endpoints lie in `V(G)`), so the crossing count is unchanged
  while the part count gains `|V(G)ᶜ|` — and `finrank_partitionConstant` is already an
  **exact** `D·|range f|`, so the extra parts are pure profit. Route, three bricks (~2–3
  commits, PanelLayer.lean beside the hub bound):
  1. *The `|range f|`-form motion bound* — the landed
     `screwDim_mul_numParts_sub_le_finrank_partitionMotions` re-proved with
     `Nat.card (Set.range f)` in place of `G.numParts f` (its proof's only use of
     `numParts` is the `hWf` step, where `finrank_partitionConstant` gives the range form
     *exactly*; everything else is verbatim):
     `(screwDim k : ℤ) * Nat.card (Set.range f) − (screwDim k − 1) * (crossingEdges f).ncard
     ≤ finrank (partitionMotions f)`, `hC` per crossing edge as landed.
  2. *Label normalization + complement separation.* (i) `partitionDef` is invariant under
     post-composition with a map injective on `f '' V(G)` (`numParts` and `crossingEdges`
     both see only labels of `V(G)`-vertices — `IsLink.left_mem`/`right_mem`), so WLOG the
     def-attaining `f` has `f '' V(G) ⊆ V(G)`; (ii) for such `f`, the refinement
     `f'' := fun x => if x ∈ V(G) then f x else x` has
     `Nat.card (range f'') = G.numParts f + (V(G))ᶜ.ncard` (the two label families are
     disjoint by (i)) and `crossingEdges f'' = crossingEdges f`.
  3. *The relative hub + B2 close*:

```lean
-- PanelLayer.lean, beside the hub bound
theorem BodyHingeFramework.screwDim_mul_compl_add_deficiency_le_finrank_infinitesimalMotions
    [Finite α] [Finite β] {n : ℕ} (F : BodyHingeFramework k α β)
    (hn : Graph.bodyBarDim n = screwDim k) (hne : V(F.graph).Nonempty)
    (hC : ∀ e u v, F.graph.IsLink e u v → F.supportExtensor e ≠ 0) :
    (screwDim k : ℤ) * (((V(F.graph))ᶜ.ncard : ℤ) + 1) + F.graph.deficiency n
      ≤ (Module.finrank ℝ F.infinitesimalMotions : ℤ)

/-- B2: the V(G)-relative deficiency upper bound on the rigidity-row span. -/
theorem BodyHingeFramework.finrank_span_rigidityRows_add_deficiency_le
    [Finite α] [Finite β] {n : ℕ} (F : BodyHingeFramework k α β)
    (hn : Graph.bodyBarDim n = screwDim k) (hne : V(F.graph).Nonempty)
    (hC : ∀ e u v, F.graph.IsLink e u v → F.supportExtensor e ≠ 0) :
    (Module.finrank ℝ (Submodule.span ℝ F.rigidityRows) : ℤ)
      ≤ screwDim k * ((V(F.graph).ncard : ℤ) - 1) - F.graph.deficiency n
```

  B2's own proof is then a 5-liner: relative hub + the extracted coannihilator complement
  (next bullet) + `ncard + ncardᶜ = card α` arithmetic. `[Nonempty α]` derives from `hne`
  inside.
* *The `D`-convention hypothesis.* `deficiency n` counts with `bodyBarDim n`, the screw side
  with `screwDim k`; the landed hub bound hard-codes `n := k + 1`
  (`bodyBarDim (k+1) = screwDim k`, its `hDcast`). The relative siblings instead take
  **`hn : Graph.bodyBarDim n = screwDim k`** — the form the use sites actually have (the
  motives carry an abstract `n`; `bodyBarDim` is strictly monotone so this is equivalent to
  `n = k + 1`, but the hypothesis form avoids an injectivity detour and matches
  `deficiency`'s parameter directly).
* *The shared complement brick.* W2 proves `finrank (span rigidityRows) + dim Z = D·|α|`
  inline; B1's reverse direction and B2's close both need it again — extract it as
  `finrank_span_rigidityRows_add_finrank_infinitesimalMotions` (GenericityDevice.lean, one
  commit with B1; W2 optionally refactored over it).

**(c) B1 — the `def = 0` bridge, exact statement.** GenericityDevice.lean, beside W2:

```lean
theorem BodyHingeFramework.isInfinitesimallyRigidOn_vertexSet_iff_finrank_span_rigidityRows
    [Finite α] (F : BodyHingeFramework k α β) (hne : V(F.graph).Nonempty) :
    F.IsInfinitesimallyRigidOn V(F.graph) ↔
      Module.finrank ℝ (Submodule.span ℝ F.rigidityRows)
        = screwDim k * (V(F.graph).ncard - 1)
```

ℕ-form RHS matching W2 (the motives' ℤ-cast at `def = 0` is a `zify`/`omega` step at use
sites, `1 ≤ ncard` from `hne`). Forward: W2 verbatim. Reverse: the complement brick turns
the row count into `dim Z = D·(|V(G)ᶜ| + 1)`, then N3
(`isInfinitesimallyRigidOn_vertexSet_of_finrank_le`). Note B1 needs **no genuine-hinge
hypothesis** in either direction (W2 and N3 take none) — `hC` enters only B2.

**(d) M2–M5 — exact statements, placements, discipline.**

* **M2** (`HasPanelRealization`, PanelHinge.lean, **root `Molecular` namespace** — it
  quantifies a `BodyHingeFramework` + a normal assignment, so the `PanelHingeFramework`
  namespace would misdirect dot-notation):

```lean
def HasPanelRealization (k n : ℕ) (G : Graph α β) : Prop :=
  ∃ (F : BodyHingeFramework k α β) (normal : α → Fin (k + 2) → ℝ),
    F.graph = G ∧
    (∀ v ∈ V(G), normal v ≠ 0) ∧
    (∀ e u v, G.IsLink e u v → F.supportExtensor e ≠ 0 ∧
      ExtensorInPanel (F.supportExtensor e) (normal u) ∧
      ExtensorInPanel (F.supportExtensor e) (normal v)) ∧
    (Module.finrank ℝ (Submodule.span ℝ F.rigidityRows) : ℤ)
      = screwDim k * ((V(G).ncard : ℤ) - 1) - G.deficiency n
```

  §1.56(b)'s design notes (i)–(iv) stand; confirmed against the carrier: the Molecular
  `BodyHingeFramework` has no `ends` field, so the relational per-link quantification is
  the only possible shape — no link-recording conjunct exists to state. The `(k, n)` pair:
  both explicit parameters; nothing relates them in the definition (the use sites' `IsMinimalKDof n k`
  facts pin `deficiency n`, and B2's `hn` pins the convention where it matters).
* **M3** (`HasGenericFullRankRealization`, in place, gains `n`, rank-form conjunct):

```lean
def HasGenericFullRankRealization (k n : ℕ) (G : Graph α β) : Prop :=
  ∃ Q : PanelHingeFramework k α β,
    Q.graph = G ∧ Q.IsGeneralPosition ∧
    ((Module.finrank ℝ (Submodule.span ℝ Q.toBodyHinge.rigidityRows) : ℤ)
      = screwDim k * ((V(G).ncard : ℤ) - 1) - G.deficiency n) ∧
    (∀ e u v, G.IsLink e u v →
      ((Q.ends e).1 = u ∧ (Q.ends e).2 = v) ∨ ((Q.ends e).1 = v ∧ (Q.ends e).2 = u)) ∧
    AlgebraicIndependent ℚ (fun p : α × Fin (k + 2) => Q.normal p.1 p.2)
```

  The rank conjunct is deliberately stated on `Q.toBodyHinge.rigidityRows` — M4's transfer
  of it to M2's `F := Q.toBodyHinge` is then **literal** (same expression). Every call site
  gains the `n` argument (mechanical; the live sites all sit at `n` already in scope from
  `IsMinimalKDof n _`).
* **M4** (the forgetful map, PanelHinge.lean, `k = 2` per (a)):

```lean
theorem hasPanelRealization_of_generic {n : ℕ} {G : Graph α β} [G.Loopless]
    (hV : 2 ≤ V(G).ncard)
    (h : PanelHingeFramework.HasGenericFullRankRealization 2 n G) :
    HasPanelRealization 2 n G
```

  Per conjunct: `F := Q.toBodyHinge`, `normal := Q.normal`; panel nonzeroness — `hV` gives
  a second body `w ∈ V(G), w ≠ v`, GP at `(v, w)` + `LinearIndependent.ne_zero`; genuine
  hinge on links — landed `supportExtensor_ne_zero_of_isGeneralPosition` via link-recording
  + `IsLink.ne` (`[G.Loopless]`, the instance the spine derives from minimality,
  `loopless_of_isMinimalKDof`); containment — the meet lemma of (a) applied at the *actual*
  `ends e` order (its two conclusions cover `{normal u, normal v}` whichever way the
  link-recording disjunct falls); rank — literal transfer. The conditioned pair becomes
  `Pc G := (G.Simple → HasGenericFullRankRealization k n G) ∧ HasPanelRealization k n G`.
* **M5** (naming/migration — *re-timed*, the one §1.56 correction of substance):
  `HasFullRankRealization` **cannot be deleted at L0** — it is the conclusion type of the
  live GenericityDevice producers (N6a and siblings) and of `theorem_55`, all of which
  restate at their own layers (L3/L5/L9 per (d)/(e) of §1.56). Decision 1's "no weak form
  survives" is a **phase-close invariant, discharged at L9** (the spine restate deletes
  `theorem_55` and the last bare-motive citations together). What L0 *does* do: take the
  weak motive **off the live conditioned spine** (the L0e pair swap below), drop its
  blueprint pin from `def:rank-hypothesis` (re-prose, (f)), and delete the now
  consumer-free old forgetful `hasFullRankRealization_of_generic` (verified: doc-comment
  references only).

**(e) The L0 slice cut** (each slice a warning-clean commit; statement-changing slices run
the structural-edit grep gate):

* **L0a** — `ExtensorInPanel` (RigidityMatrix.lean) + the meet-decomposition lemma + its
  perp-pair sub-brick (PanelLayer.lean). Purely additive. The double-annihilator step is
  the slice's one search item.
* **L0b** — the complement brick + B1 (GenericityDevice.lean). Additive.
* **L0c** — the `|range f|` motion bound + the normalization/refinement bricks + the
  relative hub + B2 (PanelLayer.lean). Additive. (Splittable in two if the partition
  bricks run long.)
* **L0d** — M2 `HasPanelRealization` + M4 `hasPanelRealization_of_generic` (PanelHinge.lean)
  + the blueprint flip of `def:genuine-hinge-realization` ((f) below). Additive +
  `checkdecls`.
* **L0e** — the in-place restates, one coordinated slice (the grep gate's home): M3's new
  conjunct + `n` parameter; `theorem_55_generic`'s conditioned pair swapped to
  `… ∧ HasPanelRealization k n G` (plumbing-only body — the pair is motive-generic);
  `theorem_55_d3`'s three bare carries re-typed to `HasPanelRealization 2 n`-shaped slots
  (they are *hypotheses*, no proofs to fix); the GP producers' conclusion seams converted
  (each ends in a `⟨Q, …, hrig, …⟩` pack — replace `hrig` by B1.mp + `hG.1`'s
  `deficiency = 0` + the cast; the conditioned IH's bare `.2` is never destructured on the
  live route, so the IH-type ripple through `case_I_realization` / `case_III_*` signatures
  is signature-only); `rankHypothesis_deficiency_of_theorem_55_d3`'s `hQrig` extraction
  re-derived through B1.mpr; the old forgetful deleted; `def:rank-hypothesis` re-prosed.
  This is the bulk slice — if it runs past one sitting, cut it M3-first (M3 + producer
  seams green with the pair *unswapped*, `theorem_55_generic` still consuming the old bare
  motive) and swap the pair in a follow-up.

**Two statement-level flags for later layers** (recorded here so the L9/L10 pins inherit
them): (i) `theorem_55_d3`'s `hD : 6 ≤ Graph.bodyBarDim n` must **tighten to
`hn : Graph.bodyBarDim n = screwDim 2`** at the L9 restate — the rank-form motive couples
the two `D` conventions through `deficiency n` in the `k > 0` strata (the `≥`-form was an
artifact of the `def = 0` rigidity-form conclusion; the `def = 0` GP producers keep their
`6 ≤` since B1 is `n`-free there). (ii) `rigidityMatrix_prop11` and the L10 feed keep the
all-`e` `hC` + `reaim` pattern unchanged — B2's per-link `hC` does not replace that
interface.

**(f) The L0 blueprint def-node dispositions.**

* **`def:genuine-hinge-realization`** (panel-layer.tex:198) — at L0d: gains
  `\lean{CombinatorialRigidity.Molecular.HasPanelRealization,
  CombinatorialRigidity.Molecular.ExtensorInPanel,
  CombinatorialRigidity.Molecular.hasPanelRealization_of_generic}` + `\leanok`; statement
  restated to the M2 form (the free-hinge carrier + per-link `ExtensorInPanel` containment
  + the ℤ-cast rank-deficiency equality, `V(G)`-relative discipline); the "*Status* …
  obligation of sub-phase 22i" paragraph deleted (it describes the pre-L0 state — and its
  sketch of the fix, "strengthen `HasFullRankRealization` to require `IsGeneralPosition`
  when simple", is *not* the §1.56 design; the restate replaces it); `\uses` gains
  `def:D-deficiency`.
* **`def:rank-hypothesis`** (panel-layer.tex:149) — at L0e: drop the
  `…HasFullRankRealization` pin (the node keeps `IsInfinitesimallyRigidOn` +
  `RankHypothesis` and gains the B1 bridge
  `…isInfinitesimallyRigidOn_vertexSet_iff_finrank_span_rigidityRows`); the "Lean form
  (bare rank)" + welded-degenerate paragraphs are replaced by the rank-form-substrate
  prose: the node now states the *shared rank form* both motives instantiate (the ℤ-cast
  row-span equality) and its `def = 0` equivalence with `IsInfinitesimallyRigidOn V(G)`
  (B1); the `V(G)`-relative paragraph survives as is.
* **`lem:trivial-motions-rank-bound`** (genericity-and-count.tex) — at L0c: the relative
  hub + B2 join its `\lean` list; one added sentence on the `V(G)`-relative form (the
  complement-separating refinement). Node stays green.
* **`thm:theorem-55` / `thm:theorem-55-d3-instance`** — untouched at L0 (their restates are
  L9's); the d3-instance's `\lean` list survives L0e verbatim (same decl names, new
  statement shapes — *this is exactly the case the structural-edit grep gate exists for*;
  the carried-family prose in the instance node should be re-checked at L0e for the
  re-typed carries and adjusted in the same commit if its hypothesis descriptions name the
  old motive).

### 1.58 The L1 signature pin — V2 resolved (`TwoEdgeConnected` = the labeling-free `cutEdges` count over nonempty proper vertex sets, connectivity included), V3 resolved (the landed swap proof is all-`k` after one re-routed contradiction; the `= 2` upgrade takes the V2 predicate as hypothesis), V4 resolved (mechanical in-place), a KT-numbering correction (the landed `splitOff_isMinimalKDof` is KT **4.8(i)**, not 4.7), KT 3.6 by a pure partition argument (no matroid direct sum), the KT-4.8(ii) cluster decomposed (the reverse forest direction KT 4.2 is the one genuinely new engine), and the L1a–L1j slice cut (2026-06-11)

> **Docs-only design pass (the L1 pin).** Lean read this pass: Deficiency.lean —
> `crossingEdges` (:245), `numParts` (:251), `partitionDef` (:258), `deficiency` (:269,
> `iSup` over labelings), `partitionDef_le_deficiency` (:304), `deficiency_nonneg` (:312),
> `IsMinimalKDof` (:359), `loopless_of_isMinimalKDof` (:370), `IsProperRigidSubgraph` (:428),
> `isKDof_zero_of_parallel_pair` (:606), `subgraph_minimality` (:684, **KT 3.3, landed** —
> its `hH : H.IsKDof n k'` is supplied as `rfl` at use sites),
> `cutLabeling`/`numParts_cutLabeling` (:746/:753), `two_le_crossingEdges_of_isKDof_zero`
> (:780, KT 3.1); ReducibleVertex.lean — `no_rigid_edge_count` (:330, KT 4.5(i); its
> `hBscard` line is the only `def = 0` use), `exists_degree_le_two` (:496),
> `crossingEdges_cutLabeling_singleton_ncard_le` (:571), `exists_degree_eq_two` (:588),
> `simple_of_isMinimalKDof_of_noRigid` (:625, G0 — its parallel-pair brick is
> `k`-independent), `exists_adjacent_degree_two_pair` (:755, consumes `no_rigid_edge_count`
> at `k = 0`); Contraction.lean — `contraction_isMinimalKDof` (:650, **already all-`k`** on
> the matroid side), `rigidContract_isMinimalKDof` (:696 — the `0` enters only via
> `change … = 0; linarith`); SplitOffDeficiency.lean — `splitOff_deficiency_le` (:62) /
> `_ge` (:197) (together = KT 4.3(i), the dichotomy `def(G̃ᵥᵃᵇ) ∈ {k−1, k}`),
> `removeVertex_deficiency_ge` (:405, KT 4.4 first half), `dof_tracking` (:545);
> ForestSurgery.lean — the acyclicity suite (:156–:484, **split direction only**),
> `isCycleSet_pair_edgeFiber_splitOff` (:354) +
> `fiber_inter_subsingleton_of_isAcyclicSet_splitOff` (:391, each forest holds ≤ 1 fiber
> copy — the WLOG-relabel key), `circuit_splitOff_meets_fiber` (:674),
> `splitOff_isMinimalKDof` (:772, **KT 4.8(i)**), `minimal_kdof_reduction[_full]`
> (:1198/:1266, the two `exists_degree_eq_two` call sites), `exists_balanced_forest_packing`
> (:1347, the `disjointed`-partition pattern), `splitOff_exists_base_inter_fiber_lt` (:1958,
> KT 4.3(ii) forward at `k = 0`), `splitOff_removeVertex_minimalKDof` (:2035);
> Operations.lean — `inducedSpan` (:51), `circuit_induces_isTight` (:174),
> `subset_edgeSet_mulTilde_inducedSpan` (:215), `circuit_induces_isRigidSubgraph` (:239),
> `fundCircuit_inducedSpan_vertexSet_eq` (:309), `matroidMG_indep_iff_exists_forest_packing`
> (:369, the forest framing KT 4.2 opens on), `rank_matroidMG_of_isKDof_zero` (:431),
> `removeVertex` (:536), `splitOff` (:579); `induce`/`restrict` semantics
> (`V(G.induce X) = X` is `rfl`). KT 2011 read **against the PDF** (printed p.N = pdf page
> N − 646): pp. 656–659 (Lemmas 3.1–3.6 with proofs), pp. 660–667 (§4 entire: 4.1–4.8 +
> Theorem 4.9 with proofs). No `.lean`/`.tex` edits this pass.

**(a) KT-numbering corrections (verified against the PDF; §1.56 cited partly from memory).**
The landed `splitOff_isMinimalKDof` is **KT 4.8(i)** (its own docstring is right; §1.56(c)'s
"unlike the landed 4.7" misnames it). The actual roster: **4.1/4.2** = the forest surgery,
split and edge-splitting (reverse) directions; **4.3** = the splitting-off dichotomy
(`G_v^{ab}` is `k`-dof or minimal `(k−1)`-dof; clause (ii) = the base criterion
`|ãb ∩ B'| < D − 1` ⟺ the `k`-dof arm) — its two-sided deficiency bound is landed
(`splitOff_deficiency_le/_ge`), its base criterion is **not** (deliberately deferred in
Phase 20 as "off the Theorem-4.9 critical path"; it comes **on** the path here, for
4.7/4.8(ii)); **4.4** = `def(G̃ᵥ) ≥ k` (landed, `removeVertex_deficiency_ge`) *plus the
equality clause* (if `= k`, some base `B` of `M(G̃)` has `|ṽb ∩ B| = 1`) — the clause is not
landed; **4.5(ii)** = at `k > 0` with no proper rigid subgraph, `Ẽ` is independent (hence
the unique base) — not landed; **4.7** = `def(G̃ᵥ) > k` (the `k = 0` arm is inline in
`splitOff_isMinimalKDof`'s `hdefGv_pos`; the `k > 0` arm needs 4.4-equality + 4.5(ii)) — not
landed; **4.8(ii)** = the `(k−1)`-decrement split — not landed. Also **KT 3.2** (a minimal
`k`-dof-graph is not 3-edge-connected, p. 657): only its `|V| = 2` consequence is needed
(the parallel class is bounded at 2); (e) pins that directly and full 3.2 is **not**
formalized.

**(b) V2 resolved: `TwoEdgeConnected` is the labeling-free cut count, connectivity
included.** The `cutLabeling` encoding needs two representative labels and a `Decidable`
instance — wrong shape for a `def`. Instead a labeling-free cut-edge set, with one transfer
lemma that makes every landed `crossingEdges`/`cutLabeling` fact available:

```lean
-- Deficiency.lean, in the `lem:two-edge-conn` section
/-- The edges of `G` crossing the cut `{V', V(G) ∖ V'}`. Labeling-free mirror of
`crossingEdges (cutLabeling V' a b)`. -/
def cutEdges (G : Graph α β) (V' : Set α) : Set β :=
  {e ∈ E(G) | ∃ x y, G.IsLink e x y ∧ x ∈ V' ∧ y ∉ V'}

/-- KT's 2-edge-connectivity in cut form, connectivity included: every nonempty proper
subset of `V(G)` is crossed by at least two edges. -/
def TwoEdgeConnected (G : Graph α β) : Prop :=
  ∀ V' : Set α, V'.Nonempty → V' ⊂ V(G) → 2 ≤ (G.cutEdges V').ncard

lemma cutEdges_eq_crossingEdges_cutLabeling {G : Graph α β} {V' : Set α} {a b : α}
    [∀ x, Decidable (x ∈ V')] (ha : a ∈ V') (hb : b ∉ V') :
    G.cutEdges V' = G.crossingEdges (cutLabeling V' a b)

theorem twoEdgeConnected_of_isKDof_zero [Finite α] {G : Graph α β} {n : ℕ}
    (hD : 1 ≤ bodyBarDim n) (hrigid : G.IsKDof n 0) : G.TwoEdgeConnected

theorem two_le_degree_of_twoEdgeConnected [Finite β] {G : Graph α β}
    (htec : G.TwoEdgeConnected) {v : α} (hv : v ∈ V(G)) (hV2 : 2 ≤ V(G).ncard) :
    2 ≤ G.degree v
```

Design notes: **(i)** connectivity is *included* automatically — a connected component `V'`
of a disconnected `G` has `cutEdges V' = ∅ < 2`, so the disconnected arm of Lemma 6.1 routes
through the same `hcut` case of the L2 principle (¬2EC), exactly as §1.56(c)(iii) wanted; at
`|V(G)| ≤ 1` the predicate is vacuous (KT's convention). **(ii)** the transfer lemma is the
single bridge: `x ∈ V' ∧ y ∉ V'` ⟺ the `cutLabeling`-labels differ (up to the `IsLink`
swap), so `twoEdgeConnected_of_isKDof_zero` is `two_le_crossingEdges_of_isKDof_zero` +
transfer (the ssubset supplies `a ∈ V' ⊆ V(G)` and `b ∈ V(G) ∖ V'`), and the degree bridge
is the landed `crossingEdges_cutLabeling_singleton_ncard_le` at the singleton cut `{v}`
(proper by `hV2`). **(iii)** `cutEdges` takes arbitrary `V' : Set α` (the `⊂ V(G)`
constraint lives in the predicate's quantifier, not the def).

**(c) V3 resolved: yes — and stronger than expected: the landed swap proof is itself
all-`k`.** The expected answer ("the average-degree half is a count") understated it: the
*edge bound* `no_rigid_edge_count` also generalizes **in place**, because its fundamental-
circuit swap never uses `def = 0` structurally. The two `0`-touching spots: `hBscard`
becomes `|Bs| = D(|V|−1) − k` (`isBase_ncard_add_deficiency_eq` verbatim, no rewrite to
`0`), and the `X ∩ ẽ ≠ ∅` step's contradiction re-routes uniformly — if `X ∩ ẽ = ∅` then
`X − ej` is `(D,D)`-tight on `V(X) = V` (`circuit_induces_isTight` +
`fundCircuit_inducedSpan_vertexSet_eq`), so it is independent of size
`D(|V|−1) ≤ rank = D(|V|−1) − k`, forcing `k ≤ 0`; with `k = def ≥ 0` (`deficiency_nonneg`)
that pins `k = 0`, whereupon `X − ej` is a *base* avoiding `ẽ` and the landed minimality
contradiction closes. One proof, no case split. In-place restates, all ReducibleVertex.lean:

```lean
theorem no_rigid_edge_count … {k : ℤ} (hD : 2 ≤ bodyBarDim n) (hVne : V(G).Nonempty)
    (hG : G.IsMinimalKDof n k) (hnp : ∀ H : Graph α β, ¬ H.IsProperRigidSubgraph G n) :
    (bodyHingeMult n : ℤ) * E(G).ncard
      < bodyBarDim n * ((V(G).ncard : ℤ) - 1) - k + bodyHingeMult n

theorem exists_degree_le_two … {k : ℤ} (hD : 3 ≤ bodyBarDim n) (hVne : V(G).Nonempty)
    (hG : G.IsMinimalKDof n k) (hnp : …) : ∃ v ∈ V(G), G.degree v ≤ 2

theorem exists_degree_eq_two … {k : ℤ} (hD : 3 ≤ bodyBarDim n) (hV2 : 2 ≤ V(G).ncard)
    (hG : G.IsMinimalKDof n k) (htec : G.TwoEdgeConnected) (hnp : …) :
    ∃ v ∈ V(G), G.degree v = 2

theorem simple_of_isMinimalKDof_of_noRigid … {k : ℤ} (hD : 2 ≤ bodyBarDim n)
    (hV : 3 ≤ V(G).ncard) (hG : G.IsMinimalKDof n k) (hnp : …) : G.Simple
```

Per lemma: `exists_degree_le_two` — the `2|E| < 3|V|` arithmetic absorbs the new `− k` via
`0 ≤ k` (derived inside from `hG.1 ▸ deficiency_nonneg`; `nlinarith` gains one term).
`exists_degree_eq_two` (the KT 4.6 restate) — the `htec` hypothesis replaces the
`two_le_crossingEdges_of_isKDof_zero` call by `two_le_degree_of_twoEdgeConnected`;
**call-site ripple is two sites** (`minimal_kdof_reduction` :1230 and
`exists_chain_data_of_noRigid`, both at `k = 0`: supply
`twoEdgeConnected_of_isKDof_zero hD1 hG.1`). G0 (`simple_of_isMinimalKDof_of_noRigid`) —
proof verbatim (`loopless_of_isMinimalKDof` is already all-`k`; the parallel-pair subgraph
is `0`-dof regardless of `G`'s `k`); zero call-site ripple (implicit `k` unifies at `0`).
`exists_adjacent_degree_two_pair` (the `d = 3` G4a consumer) stays at `k = 0` but its
`hedge` term gains `− 0` — minor body touch-up in the same commit. `exists_degree_eq_two`
keeps `hnp` (KT 4.6's chain alternative is not needed: the project's form already
specializes to the bare degree-2 vertex).

**(d) V4 resolved: mechanical.** `contraction_isMinimalKDof` (the matroid side) is
*already* all-`k`; the graph bridge generalizes in place —

```lean
theorem rigidContract_isMinimalKDof … {k : ℤ} (hG : G.IsMinimalKDof n k)
    (hH : H.IsProperRigidSubgraph G n) {r : α} (hr : r ∈ V(H)) :
    (G.rigidContract H r).IsMinimalKDof n k
```

— the only `0`-specific proof line is `change (G.rigidContract H r).deficiency n = 0`; it
becomes `… = k` and the same `linarith [hbridge, hcons]` closes (`hcons` already carries
`k`). Call sites (CaseI.lean :2243 area) unify at `k = 0`, zero ripple. Blueprint:
`lem:rigidContract-isMinimalKDof` (case-i.tex:456) restates all-`k` in the same commit
(statement-grep gate).

**(e) The `|V| ≤ 2` trichotomy (KT p. 671 base + the Lemma-3.2 consequence).** Three bricks
+ one packaging, Deficiency.lean beside `isKDof_zero_of_parallel_pair`:

```lean
/-- With no edges every partition's deficiency is `D(|P|−1)`, maximized by the discrete
partition (`f = id`): `def(G̃) = D(|V(G)|−1)`. -/
theorem deficiency_of_edgeSet_empty [Finite α] {G : Graph α β} {n : ℕ}
    (hne : V(G).Nonempty) (hE : E(G) = ∅) :
    G.deficiency n = (bodyBarDim n : ℤ) * ((V(G).ncard : ℤ) - 1)

/-- A single edge on two vertices: the two-part cut crosses once, `def = D − (D−1) = 1`. -/
theorem deficiency_of_single_edge [Finite α] {G : Graph α β} {n : ℕ}
    (hD : 1 ≤ bodyBarDim n) {x y : α} (hxy : x ≠ y) {e : β}
    (hl : G.IsLink e x y) (hV : V(G) = {x, y}) (hE : E(G) = {e}) :
    G.deficiency n = 1

/-- The Lemma-3.2 consequence: at `|V| = 2`, minimality bounds the parallel class at 2. -/
theorem edgeSet_ncard_le_two_of_isMinimalKDof_of_ncard_two [DecidableEq β] [Finite α]
    [Finite β] {G : Graph α β} {n : ℕ} {k : ℤ} (hD : 2 ≤ bodyBarDim n)
    (hG : G.IsMinimalKDof n k) (hV : V(G).ncard = 2) : E(G).ncard ≤ 2

theorem isMinimalKDof_ncard_le_two_trichotomy [DecidableEq β] [Finite α] [Finite β]
    {G : Graph α β} {n : ℕ} {k : ℤ} (hD : 2 ≤ bodyBarDim n)
    (hG : G.IsMinimalKDof n k) (hne : V(G).Nonempty) (hV : V(G).ncard ≤ 2) :
    (E(G) = ∅ ∧ k = bodyBarDim n * ((V(G).ncard : ℤ) - 1)) ∨
    (∃ x y e, x ≠ y ∧ V(G) = {x, y} ∧ E(G) = {e} ∧ G.IsLink e x y ∧ k = 1) ∨
    (∃ x y e f, x ≠ y ∧ e ≠ f ∧ V(G) = {x, y} ∧ E(G) = {e, f} ∧
      G.IsLink e x y ∧ G.IsLink f x y ∧ k = 0)
```

Design notes: **(i)** the first disjunct covers `ncard ∈ {1, 2}` uniformly (`k = 0` resp.
`k = D`): at `ncard = 1` looplessness (`loopless_of_isMinimalKDof`) forces `E = ∅`.
**(ii)** the parallel-class bound's proof is *not* full KT 3.2: with three distinct edges
(all linking `x, y` by looplessness + `hV`), restrict to two — `H := G.restrict {e₁, e₂}`
is `0`-dof (`isKDof_zero_of_parallel_pair`), `rank M(H̃) = D`
(`rank_matroidMG_of_isKDof_zero`), a base `B_H` of `M(H̃)` is `M(G̃)`-independent
(`matroidMG_restrict_mulTilde` + `restrict_le`) of size `D ≤ rank M(G̃) = D − k`, forcing
`k = 0` (nonneg), whence `B_H` is a base of `M(G̃)` avoiding `ẽ₃` — contradicting `hG.2`.
**(iii)** the `k`-values come from the deficiency computations (`hG.1` pins `def = k`); the
parallel-pair arm reuses `isKDof_zero_of_parallel_pair` on `G` itself. **(iv) the L2 floor
flag (recorded here for the L2 pin):** §1.56(c)'s design note (i) ("the vertex floor drops
to nothing") over-reaches at `V(G) = ∅`: with `α` empty, `deficiency` is an `iSup` over the
empty labeling type — junk, and M2's rank conjunct is then *false* of the empty framework,
so `hbase` would be undischargeable. The L2 principle should conclude
`∀ k G, IsMinimalKDof n k → V(G).Nonempty → P G` with `hbase` covering `1 ≤ ncard ≤ 2` —
KT-faithful, and sound because Lemma 6.1's cut sides are nonempty *by construction* (the IH
is never applied to an empty graph).

**(f) The cut-edge decomposition (KT Lemma 3.6, p. 659) — a pure partition argument, no
matroid direct sum.** KT route the equality through `M(G̃) = M(G̃₁) ⊕ M(G̃₂) ⊕ M(G̃₃)` (via
"no circuit crosses the cut", Lemmas 3.1 + 3.4). The project does **not** need the direct
sum: both inequalities fall to the landed `partitionDef` machinery. The `≥` direction
combines optimal side-partitions (attained, `exists_eq_ciSup_of_finite`) into one
side-separated labeling; the `≤` direction refines an arbitrary labeling to a
side-separated one without decreasing `partitionDef` (here `d_G(P) ≤ 1` enters: the
refinement gains `D` per straddling part split and pays at most `D − 1` for the at-most-one
cut edge newly crossing), then splits exactly. Five bricks + packaging, Deficiency.lean,
new subsection after the two-edge-connectivity section:

```lean
/-- `partitionDef` reads `f` only on `V(G)`. -/
lemma partitionDef_congr {G : Graph α β} {n : ℕ} {f g : α → α}
    (h : Set.EqOn f g V(G)) : G.partitionDef n f = G.partitionDef n g

/-- Relabeling invariance: post-composition with a map injective on the carried labels. -/
lemma partitionDef_comp_of_injOn {G : Graph α β} {n : ℕ} {f g : α → α}
    (hg : Set.InjOn g (f '' V(G))) : G.partitionDef n (g ∘ f) = G.partitionDef n f

/-- The exact split of a side-separated labeling: parts and crossings decompose over
`{V₁, V(G) ∖ V₁}`, every cut edge crossing. -/
lemma partitionDef_split_of_sides {G : Graph α β} {n : ℕ} {V₁ : Set α} {g : α → α}
    (hsub : V₁ ⊆ V(G)) (hsep : ∀ x ∈ V₁, ∀ y ∈ V(G) \ V₁, g x ≠ g y) :
    G.partitionDef n g
      = (G.induce V₁).partitionDef n g + (G.induce (V(G) \ V₁)).partitionDef n g
        + bodyBarDim n - (bodyBarDim n - 1) * (G.cutEdges V₁).ncard

/-- The side-refinement does not decrease `partitionDef` when at most one edge crosses. -/
lemma exists_sides_separated_partitionDef_le [Finite α] {G : Graph α β} {n : ℕ}
    {V₁ : Set α} (hsub : V₁ ⊆ V(G)) (hcut : (G.cutEdges V₁).ncard ≤ 1) (f : α → α) :
    ∃ g : α → α, (∀ x ∈ V₁, ∀ y ∈ V(G) \ V₁, g x ≠ g y) ∧
      G.partitionDef n f ≤ G.partitionDef n g

/-- KT Lemma 3.6, both arms (`d_G(P) = 1`: `k = k₁ + k₂ + 1`; `d_G(P) = 0`: `+ D`). -/
theorem deficiency_eq_of_cutEdges_ncard_le_one [Finite α] [Finite β] {G : Graph α β}
    {n : ℕ} (hD : 1 ≤ bodyBarDim n) {V₁ : Set α} (hne : V₁.Nonempty)
    (hssub : V₁ ⊂ V(G)) (hcut : (G.cutEdges V₁).ncard ≤ 1) :
    G.deficiency n
      = (G.induce V₁).deficiency n + (G.induce (V(G) \ V₁)).deficiency n
        + bodyBarDim n - (bodyBarDim n - 1) * (G.cutEdges V₁).ncard

/-- The `hcut` producer's opener: cut decomposition + KT 3.3 sides-minimal. -/
theorem exists_cut_decomposition_of_not_twoEdgeConnected [DecidableEq β] [Finite α]
    [Finite β] {G : Graph α β} {n : ℕ} {k : ℤ} (hD : 1 ≤ bodyBarDim n)
    (hG : G.IsMinimalKDof n k) (hntec : ¬ G.TwoEdgeConnected) :
    ∃ (V₁ : Set α) (k₁ k₂ : ℤ), V₁.Nonempty ∧ V₁ ⊂ V(G) ∧ (V(G) \ V₁).Nonempty ∧
      (G.induce V₁).IsMinimalKDof n k₁ ∧
      (G.induce (V(G) \ V₁)).IsMinimalKDof n k₂ ∧
      (G.cutEdges V₁).ncard ≤ 1 ∧
      k = k₁ + k₂ + bodyBarDim n - (bodyBarDim n - 1) * (G.cutEdges V₁).ncard
```

Proof routes: *split* — `numParts` decomposes because the two sides' label images are
disjoint (`hsep`); `crossingEdges G g` is the disjoint union of the two sides' crossing
sets and `cutEdges V₁` (each cut edge crosses by `hsep`; the edge trichotomy "within `V₁` /
within the complement / crossing" is an inline classification over `edgeSet_induce`); the
`ℤ` arithmetic is `ring`-level. *Refinement* — `g x := rep (f x, side x)` choosing one
representative vertex per (part ∩ side) piece (distinct pieces are disjoint nonempty vertex
sets, so representatives are automatically distinct — the L0c relative-hub normalization
pattern); `Δ = D·s − (D−1)·(d_g − d_f)` with `s` = the number of straddling parts;
`d_g − d_f ≤ 1` (only a cut edge inside an `f`-part can newly cross, and there is at most
one) and `d_g > d_f` forces `s ≥ 1`, so `Δ ≥ 0`. *Equality* — `≤` by `ciSup_le` ∘
refinement ∘ split ∘ `partitionDef_le_deficiency` per side; `≥` by attained side-optima
`f₁, f₂` (`exists_eq_ciSup_of_finite`), normalized into the sides
(`Set.Finite.exists_injOn_of_encard_le` injections `fᵢ '' Vᵢ ↪ Vᵢ` +
`partitionDef_comp_of_injOn` + `partitionDef_congr`), combined piecewise and split.
*Packaging* — ¬2EC unfolds to the `V₁` witness with `ncard < 2`; sides-minimal is the
landed `subgraph_minimality (G.induce_le hsub) hG rfl` (the
`splitOff_removeVertex_minimalKDof` idiom); complement nonemptiness falls out of the
ssubset. The L4 producer additionally reads `0 ≤ k₁, k₂` (`deficiency_nonneg`, sides
nonempty) and `|Vᵢ| < |V(G)|` (proper) — both one-liners at the use site, not packaged.

**(g) The KT-4.8(ii) cluster — decomposed; the reverse forest direction (KT 4.2) is the one
genuinely new engine.** Everything else rides on landed machinery. The dependency chain
(statements below): 4.2(i)/(ii) → {4.4-equality, 4.3(ii)-reverse}; 4.5(ii) (independent of
4.2) → with 4.4-equality → 4.7 all-`k`; 4.3(ii)-forward (mechanical generalization) + 4.7 +
4.2(ii) + the commuting square → 4.8(ii).

* **KT 4.2, the edge-splitting extension (NEW, the forest core).** Stated over the
  project's `splitOff` — no new graph operation: `G` *is* the edge-split of
  `G.splitOff v a b e₀` along `e₀`, so the lemma takes the standing degree-2 data and
  converts split-side independence back up. ForestSurgery.lean:

  ```lean
  theorem splitOff_indep_extend_of_fiber_lt [DecidableEq β] [Finite α] [Finite β]
      {G : Graph α β} {n : ℕ} (hD : 2 ≤ bodyBarDim n) {v a b : α} {eₐ e_b e₀ : β}
      (hab : a ≠ b) (hav : a ≠ v) (hbv : b ≠ v) (heab : eₐ ≠ e_b)
      (hla : G.IsLink eₐ v a) (hlb : G.IsLink e_b v b)
      (hdeg2 : ∀ e x, G.IsLink e v x → e = eₐ ∨ e = e_b) (he₀ : e₀ ∉ E(G))
      {I' : Set (β × Fin (bodyHingeMult n))}
      (hI' : ((G.splitOff v a b e₀).matroidMG n).Indep I')
      (hlt : (I' ∩ edgeFiber e₀ n).ncard < bodyHingeMult n) :
      ∃ I, (G.matroidMG n).Indep I ∧ I.ncard = I'.ncard + bodyBarDim n ∧
        (I ∩ edgeFiber e_b n).ncard = (I' ∩ edgeFiber e₀ n).ncard + 1 ∧
        I \ (edgeFiber eₐ n ∪ edgeFiber e_b n) = I' \ edgeFiber e₀ n

  theorem splitOff_indep_extend_of_fiber_subset  -- same data; the h' = D − 1 case
      … (hI' : Indep I') (hsub : edgeFiber e₀ n ⊆ I') :
      ∃ I, (G.matroidMG n).Indep I ∧ I.ncard + 1 = I'.ncard + bodyBarDim n ∧
        I \ (edgeFiber eₐ n ∪ edgeFiber e_b n) = I' \ edgeFiber e₀ n
  ```

  The *survivor conjunct* (`I` and `I'` agree off the three special fibers) is free from
  the construction and carries the 4.8(ii) minimality transport (a base avoiding `ẽ`
  extends to a base still avoiding `ẽ`). KT's construction (pp. 660–661): partition `I'`
  into `D` forests (`matroidMG_indep_iff_exists_forest_packing`, made disjoint by the
  landed `disjointed` pattern of `exists_balanced_forest_packing`); each forest holds
  **≤ 1** `ẽ₀`-copy (the landed `fiber_inter_subsingleton_of_isAcyclicSet_splitOff` — two
  parallel copies form a cycle), so after a forest-reindex + fiber-relabel WLOG the `h'`
  copies are `(e₀)ᵢ ∈ F'ᵢ`, `i ≤ h'`; extend `Fᵢ = F'ᵢ − (e₀)ᵢ + (eₐ)ᵢ + (e_b)ᵢ` for
  `i ≤ h'`, `Fᵢ = F'ᵢ + (eₐ)ᵢ` for `h' < i ≤ D−1`, `F_D = F'_D + (e_b)_{h'+1}` (case (ii):
  swap all `D − 1`, `F_D = F'_D`). Two **new reverse-direction acyclicity bricks**: (A)
  *pendant insert* — a `v`-avoiding `G̃`-forest absorbs one `(eₐ)ᵢ` or `(e_b)ᵢ` copy
  (mirror of the landed `acyclicSet_insert_vfiber_of_not_inc`, which is stated for the
  descent's context — adapt or re-derive); (B) *the through-`v` swap* — `F'` acyclic in
  `G̃ᵥᵃᵇ` with `(e₀)ᵢ ∈ F'` makes `F' − (e₀)ᵢ + (eₐ)ᵢ + (e_b)ᵢ` acyclic in `G̃` (removing
  a forest edge separates `a` from `b`; the fresh `v` re-joins them — mirror of the landed
  forward reroute `isAcyclicSet_splitOff_reroute`). The cardinality bookkeeping is the
  disjoint-union count `I = (I' ∖ ẽ₀-used) ∪ (D−1 eₐ-copies) ∪ (h'+1 e_b-copies)`.

* **KT 4.5(ii) (NEW, cheap).** ReducibleVertex.lean beside `no_rigid_edge_count`:

  ```lean
  theorem indep_edgeSet_mulTilde_of_noRigid_of_pos [DecidableEq β] [Finite α] [Finite β]
      {G : Graph α β} {n : ℕ} {k : ℤ} (hD : 2 ≤ bodyBarDim n)
      (hG : G.IsMinimalKDof n k) (hk : 0 < k)
      (hnp : ∀ H : Graph α β, ¬ H.IsProperRigidSubgraph G n) :
      (G.matroidMG n).Indep E(G.mulTilde n)

  theorem isBase_eq_edgeSet_mulTilde_of_noRigid_of_pos  -- the uniqueness corollary
      … {B} (hB : (G.matroidMG n).IsBase B) : B = E(G.mulTilde n)
  ```

  Proof: dependence yields a circuit `C ⊆ Ẽ`; `circuit_induces_isRigidSubgraph` + `hnp` +
  looplessness (`2 ≤ |V(C)|`) force `V(C) = V(G)`, so `G` carries a spanning rigid
  subgraph: `rank M(G̃) ≥ D(|V|−1)` (`rank_matroidMG_of_isKDof_zero` through
  `matroidMG_restrict_mulTilde`), so `def ≤ 0`, contradicting `hk`. Uniqueness: `Ẽ`
  independent + `B ⊆ Ẽ` + `IsBase.eq_of_subset_indep`.

* **KT 4.4-equality (NEW; 4.2(i) at `h' = 0`).** ForestSurgery.lean:

  ```lean
  theorem exists_isBase_vb_fiber_eq_one_of_removeVertex_isKDof … {k : ℤ}
      (hD : 2 ≤ bodyBarDim n) [degree-2 data + he₀] (hG : G.IsKDof n k)
      (hGv : (G.removeVertex v).IsKDof n k) :
      ∃ B, (G.matroidMG n).IsBase B ∧ (B ∩ edgeFiber e_b n).ncard = 1
  ```

  A base `B'` of `M(G̃ᵥ)` is `M(G̃ᵥᵃᵇ)`-independent (`mulTilde_removeVertex_le_splitOff` +
  `matroidMG_restrict_mulTilde`) with `B' ∩ ẽ₀ = ∅`; 4.2(i) lifts it to `M(G̃)`-independent
  `I` of size `|B'| + D = D(|V∖v|−1) − k + D = D(|V|−1) − k = rank M(G̃)`
  (`rank_add_deficiency_eq` both sides), so `I` is a base (`Indep.isBase_of_ncard`) with
  `|I ∩ ẽ_b| = 0 + 1`.

* **KT 4.7 all-`k` (NEW assembly).** ForestSurgery.lean:

  ```lean
  theorem removeVertex_deficiency_gt_of_noRigid … {k : ℤ} (hD : 3 ≤ bodyBarDim n)
      (hV3 : 3 ≤ V(G).ncard) [degree-2 data + he₀] (hG : G.IsMinimalKDof n k)
      (hnp : …) : k < (G.removeVertex v).deficiency n
  ```

  `k = 0` arm: extract the landed inline (`splitOff_isMinimalKDof`'s `hdefGv_pos`: `G_v` is
  a proper subgraph on `≥ 2` vertices, so `hnp` forbids `def(G̃ᵥ) = 0`; nonneg gives `> 0`).
  `k > 0` arm: `≥ k` is the landed `removeVertex_deficiency_ge`; equality would give a base
  `B` with `|ẽ_b ∩ B| = 1` (4.4-equality), but every base is `Ẽ` (4.5(ii) uniqueness) with
  `|ẽ_b ∩ Ẽ| = D − 1 ≥ 2` (`edgeFiber_ncard`, `hD`) — contradiction. (`hD : 3 ≤ D` is
  sharp: at `D = 2`, `D − 1 = 1` and the contradiction vanishes; the molecular regime is
  `D ≥ 6` anyway.)

* **KT 4.3(ii), both directions.** Forward — the landed
  `splitOff_exists_base_inter_fiber_lt` restates **in place** at general `k`: hypotheses
  `(hG : G.IsKDof n k)` and `(hH : (G.splitOff v a b e₀).IsKDof n k)` (the landed `k = 0`
  form derived `hH` internally from `splitOff_deficiency_le` + nonneg; the general form
  takes it — its one consumer, `splitOff_removeVertex_minimalKDof` :2061, supplies its
  internal `hdefH_zero`). The rank arithmetic is the same `forest_surgery_count` reroute
  with `rank = D(|V∖v|−1) − k`. Reverse — NEW (needs 4.2(i)):

  ```lean
  theorem splitOff_isKDof_of_exists_base_inter_fiber_lt … {k : ℤ}
      (hG : G.IsKDof n k) {B'} (hB' : ((G.splitOff v a b e₀).matroidMG n).IsBase B')
      (hlt : (B' ∩ edgeFiber e₀ n).ncard < bodyHingeMult n) :
      (G.splitOff v a b e₀).IsKDof n k
  ```

  (4.2(i) lifts `B'` to `M(G̃)`-independent of size `D(|V|−1) − def(G̃ᵥᵃᵇ)`, so
  `k = def(G̃) ≤ def(G̃ᵥᵃᵇ)`; with the landed `splitOff_deficiency_le`, equality.)

* **The commuting square (NEW, small).** Operations.lean beside `splitOff` — needed because
  4.8(ii)'s edge-split happens *inside a subgraph*:

  ```lean
  lemma induce_insert_splitOff {G : Graph α β} {v a b : α} {e₀ : β} {S : Set α}
      (hvS : v ∉ S) (haS : a ∈ S) (hbS : b ∈ S) (he₀ : e₀ ∉ E(G)) :
      (G.induce (insert v S)).splitOff v a b e₀ = (G.splitOff v a b e₀).induce S
  ```

  `Graph.ext`: both vertex sets are `S`; both link relations are "`G`-links avoiding `v`
  with ends in `S`, plus the `e₀`-link at `(a, b)`".

* **KT 4.8(ii), the assembly (NEW).** ForestSurgery.lean beside `splitOff_isMinimalKDof`:

  ```lean
  theorem splitOff_isMinimalKDof_of_pos [DecidableEq β] [Finite α] [Finite β]
      {G : Graph α β} {n : ℕ} {k : ℤ} (hD : 3 ≤ bodyBarDim n) (hV3 : 3 ≤ V(G).ncard)
      (hk : 0 < k) {v a b : α} {eₐ e_b e₀ : β}
      (hab : a ≠ b) (hav : a ≠ v) (hbv : b ≠ v) (haV : a ∈ V(G)) (hbV : b ∈ V(G))
      (hvG : v ∈ V(G)) (heab : eₐ ≠ e_b) (hla : G.IsLink eₐ v a) (hlb : G.IsLink e_b v b)
      (hdeg2 : ∀ e x, G.IsLink e v x → e = eₐ ∨ e = e_b) (he₀ : e₀ ∉ E(G))
      (hG : G.IsMinimalKDof n k) (hnp : ∀ H : Graph α β, ¬ H.IsProperRigidSubgraph G n) :
      (G.splitOff v a b e₀).IsMinimalKDof n (k - 1)
  ```

  Route (KT pp. 665–666, against the landed inventory): **(1)** `def(H) ∈ {k−1, k}`
  (`dof_tracking` + `hG.1`). **(2)** rule out `k`: if `def(H) = k`, 4.3(ii)-forward gives a
  base `B'` with `|B' ∩ ẽ₀| < D − 1`, so some copy `p ∈ ẽ₀ ∖ B'`; `X := fundCircuit p B'`;
  `G' := H.inducedSpan n X` is rigid in `H` (`circuit_induces_isRigidSubgraph`);
  `V(G') = V(H)` would make `def(H) ≤ 0 < k` (the spanning-rigid rank argument of 4.5(ii)),
  so `V(G') ⊊ V(H)`; `a, b ∈ V(G')` (`p ∈ X` and `e₀` links `a, b`); set
  `K := G.induce (insert v V(G'))` — the commuting square identifies `K.splitOff v a b e₀`
  with `G'`, and `I := X ∖ {p}` is `M(G̃')`-independent
  (`subset_edgeSet_mulTilde_inducedSpan` + restriction) with
  `|I ∩ ẽ₀| ≤ |B' ∩ ẽ₀| < D − 1` and `|I| = D(|V(G')|−1)` (`circuit_induces_isTight`);
  4.2(i) at `K` lifts to `M(K̃)`-independent of size `D(|V(K)|−1)`, so `def(K̃) ≤ 0` and `K`
  is a **proper rigid subgraph of `G`** (`insert v V(G') ⊊ V(G)` from
  `V(G') ⊊ V(H) = V(G) ∖ {v}`; `2 ≤ |V(K)|` from `a, v`) — contradicting `hnp`. **(3)**
  minimality at `def(H) = k − 1`: a base `B'` of `M(H̃)` avoiding `ẽ` — case `e = e₀`:
  `B' ⊆ E(G̃ᵥ)` (`edgeSet_mulTilde_splitOff_diff_fiber`), so
  `rank M(G̃ᵥ) ≥ |B'| = D(|V∖v|−1) − (k−1)`, i.e. `def(G̃ᵥ) ≤ k − 1 < k`, contradicting
  4.7; case `e ≠ e₀`: `ẽ₀ ⊆ B'` (else 4.3(ii)-reverse gives `def(H) = k`), so 4.2(ii)
  lifts `B'` to an `M(G̃)`-independent `J` of size `D(|V|−1) − k = rank` — a base — whose
  survivor conjunct gives `J ∩ ẽ = B' ∩ ẽ = ∅` (distinct fibers are disjoint,
  `e ∉ {eₐ, e_b, e₀}`), contradicting `hG.2`.

**(h) Blueprint dispositions (structural-edit mode; each lands with its Lean slice).** New
nodes — deficiency.tex `sec:molecular-deficiency-rigid`: `def:cut-edges-2ec` (the (b)
suite; `lem:two-edge-conn` gains one pointer sentence), `lem:two-vertex-trichotomy` (the
(e) suite), `lem:cut-edge-decomposition` (the (f) suite, one node, `\lean`-listing the
bricks + packaging); molecular-induction.tex: `lem:edge-splitting` (the KT 4.2 pair, in
`sec:molecular-induction-forest`; `rem:kt-lemma-41`'s "the matroid-base form … is off the
Theorem-4.9 critical path" sentence gains the qualifier "…and comes on the path for the
all-`k` layer (Phase 22i L1)"), `lem:edge-set-indep-pos` (4.5(ii) + uniqueness),
`lem:removal-deficiency-strict` (4.7; sibling of `lem:removal-deficiency`, which keeps
4.4's `≥` half — the 4.4-equality clause joins the new node's `\lean` list),
`lem:splitoff-kdof-criterion` (4.3(ii) forward restate + reverse), `lem:reduction-step-pos`
(4.8(ii), beside `lem:reduction-step`). Restated **in place** (the statement-grep gate per
slice): `lem:no-rigid-edge-count`, `lem:low-degree-vertex`, `lem:reducible-vertex` (gains
the 2EC hypothesis), `lem:simple-minimal-noRigid` (molecular-induction.tex);
`lem:rigidContract-isMinimalKDof` (case-i.tex).

**(i) The L1 slice cut** (each a warning-clean commit; statement-changing slices run the
structural-edit grep gate):

* **L1a** — V2: `cutEdges` + `TwoEdgeConnected` + the three bridges (Deficiency.lean) +
  `def:cut-edges-2ec`. Additive. *Buildable.*
* **L1b** — the `|V| ≤ 2` trichotomy: the two deficiency computations, the parallel-class
  bound, the packaging (Deficiency.lean) + `lem:two-vertex-trichotomy`. Additive.
  *Buildable.*
* **L1c** — the in-place all-`k` restates (V3 + V4 + G0): `no_rigid_edge_count`,
  `exists_degree_le_two`, `exists_degree_eq_two` (2EC hypothesis; two call sites + the
  `exists_adjacent_degree_two_pair` body touch-up), `simple_of_isMinimalKDof_of_noRigid`,
  `rigidContract_isMinimalKDof` + the five blueprint restates. Needs L1a. *Buildable;
  splittable* (degree suite / contract bridge) *if it runs long.*
* **L1d** — KT 3.6 part 1: `partitionDef_congr`, `partitionDef_comp_of_injOn`,
  `partitionDef_split_of_sides` (Deficiency.lean). Additive. *Buildable.*
* **L1e** — KT 3.6 part 2: the refinement bound, `deficiency_eq_of_cutEdges_ncard_le_one`,
  the ¬2EC packaging + `lem:cut-edge-decomposition`. Needs L1a + L1d. *Buildable.*
* **L1f** — KT 4.5(ii) + base uniqueness + `lem:edge-set-indep-pos`. Additive. *Buildable.*
* **L1g** — the reverse acyclicity bricks (pendant insert + the through-`v` swap,
  ForestSurgery.lean). Additive. *Buildable — the watch item: mirrors of landed lemmas, but
  the cycle-lift bookkeeping is where the forward direction spent its budget.*
* **L1h** — KT 4.2(i)/(ii) (`splitOff_indep_extend_of_fiber_lt` / `_subset`) +
  `lem:edge-splitting`. Needs L1g. *Buildable; the WLOG forest-reindex/fiber-relabel is the
  fiddly half — keep the `disjointed` partition from the start.*
* **L1i** — KT 4.4-equality + 4.7 all-`k` + 4.3(ii) forward-restate + reverse +
  `lem:removal-deficiency-strict` / `lem:splitoff-kdof-criterion`. Needs L1f + L1h.
  *Buildable.*
* **L1j** — the commuting square + the 4.8(ii) assembly + `lem:reduction-step-pos`. Needs
  L1h + L1i (+ the L1f rank argument). *Buildable.*

Build order: **L1a → {L1b, L1c, L1d, L1f, L1g} (independent) → L1e, L1h → L1i → L1j.**
~10 commits. L1's outputs feed L2 (`minimal_kdof_reduction_all_k` consumes the V2 predicate
and the (e) floor flag), L3 (the trichotomy), L4 (the cut decomposition), and L6 (the
4.6-restate + 4.8(ii)).

### 1.59 The L2 signature pin — `minimal_kdof_reduction_all_k` pinned with the §1.58(e)(iv) floor flag implemented (conclude at `V(G).Nonempty`, `hbase` covers `1 ≤ ncard ≤ 2`, **and the IH carries the same `Nonempty` guard** — the one statement-level delta the flag forces beyond its own wording); the five-slot-vs-landed-inventory audit clean; the principle needs no `hD`/`hfresh`/`[Finite β]` (the `_full` precedent); the legacy `minimal_kdof_reduction[_full]` stays beside it, neither derivable from the other; blueprint: NEW node `thm:minimal-kdof-reduction-all-k` (2026-06-12)

> **Docs-only design pass (the L2 pin).** Lean read this pass (declarations, current line
> numbers): ForestSurgery.lean — `minimal_kdof_reduction` (:2293, the 0-dof three-case
> principle: `hD`/`hfresh`, value-IH `hsplit`, conclusion at `2 ≤ ncard`),
> `minimal_kdof_reduction_full` (:2362, the (β)-interface variant — **no `hD`/`hfresh`/
> `[Finite β]`**, full IH to both branches; its strong-induction pattern
> `induction hN : V(G).ncard using Nat.strong_induction_on generalizing G` is the skeleton
> L2 reuses with `k` added to the `generalizing`), `splitOff_isMinimalKDof` (:1867, KT
> 4.8(i)), `splitOff_isMinimalKDof_of_pos` (:3399, KT 4.8(ii), landed L1j);
> Deficiency.lean — `deficiency_nonneg` (:312, needs `[Finite α]` + `V(G).Nonempty`),
> `IsKDof` (:350, defeq `G.deficiency n = k`), `IsMinimalKDof` (:359, `[DecidableEq β]`),
> `IsProperRigidSubgraph` (:428), `cutEdges` (:851), `TwoEdgeConnected` (:859, a bare `Prop`
> — classical `by_cases` suffices), `twoEdgeConnected_of_isKDof_zero` (:899),
> `exists_cut_decomposition_of_not_twoEdgeConnected` (:1507, landed L1e),
> `isMinimalKDof_ncard_le_two_trichotomy` (:2233, landed L1b); Contraction.lean —
> `rigidContract_isMinimalKDof` (:696, all-`k`, landed L1c — note the instance hypothesis
> `[NeZero (bodyHingeMult n)]` in place of an explicit `hD`); ReducibleVertex.lean —
> `exists_degree_eq_two` (:673, all-`k` with `htec`, landed L1c),
> `simple_of_isMinimalKDof_of_noRigid` (:698, all-`k`, landed L1c). KT re-read against the
> PDF: p. 671 (§6 opening — the base trichotomy, **the four-case `|V| ≥ 3` split verbatim**,
> IH (6.1) over every nonnegative `k_H`). Blueprint read: molecular-induction.tex
> `sec:molecular-induction-thm49` (:1222–1268, `thm:minimal-kdof-reduction`);
> deficiency.tex labels (`def:k-dof` :86, `def:rigid-subgraph` :105, `def:cut-edges-2ec`
> :152). No `.lean`/`.tex` edits this pass.

**(a) The pinned statement.** ForestSurgery.lean, directly after
`minimal_kdof_reduction_full`, in the same section:

```lean
/-- KT's four-case all-`k` induction skeleton (KT 2011 p. 671, §6 opening + IH (6.1)). -/
theorem minimal_kdof_reduction_all_k [DecidableEq β] [Finite α] {n : ℕ}
    {P : Graph α β → Prop}
    (hbase : ∀ (k : ℤ) (G : Graph α β), G.IsMinimalKDof n k → V(G).Nonempty →
      V(G).ncard ≤ 2 → P G)
    (hcut : ∀ (k : ℤ) (G : Graph α β), G.IsMinimalKDof n k → 3 ≤ V(G).ncard →
      ¬ G.TwoEdgeConnected →
      (∀ (k' : ℤ) (G' : Graph α β), G'.IsMinimalKDof n k' → V(G').Nonempty →
        V(G').ncard < V(G).ncard → P G') → P G)
    (hcontract : ∀ (k : ℤ) (G : Graph α β), G.IsMinimalKDof n k → 3 ≤ V(G).ncard →
      (∃ H : Graph α β, H.IsProperRigidSubgraph G n) →
      (∀ (k' : ℤ) (G' : Graph α β), G'.IsMinimalKDof n k' → V(G').Nonempty →
        V(G').ncard < V(G).ncard → P G') → P G)
    (hsplitPos : ∀ (k : ℤ) (G : Graph α β), G.IsMinimalKDof n k → 0 < k →
      3 ≤ V(G).ncard → G.TwoEdgeConnected →
      (∀ H : Graph α β, ¬ H.IsProperRigidSubgraph G n) →
      (∀ (k' : ℤ) (G' : Graph α β), G'.IsMinimalKDof n k' → V(G').Nonempty →
        V(G').ncard < V(G).ncard → P G') → P G)
    (hsplitZero : ∀ G : Graph α β, G.IsMinimalKDof n 0 → 3 ≤ V(G).ncard →
      G.TwoEdgeConnected → (∀ H : Graph α β, ¬ H.IsProperRigidSubgraph G n) →
      (∀ (k' : ℤ) (G' : Graph α β), G'.IsMinimalKDof n k' → V(G').Nonempty →
        V(G').ncard < V(G).ncard → P G') → P G) :
    ∀ (k : ℤ) (G : Graph α β), G.IsMinimalKDof n k → V(G).Nonempty → P G
```

Design notes: **(i) the floor flag, fully unfolded.** §1.58(e)(iv) recorded "conclude at
`V(G).Nonempty` with `hbase` covering `1 ≤ ncard ≤ 2`"; implementing it forces one further
statement-level consequence the flag's wording leaves implicit: **the IH must carry the same
`Nonempty` guard** — inside the strong induction the IH is exactly the conclusion-at-smaller-
`ncard`, and the conclusion now holds only for nonempty graphs. This *weakens* the
obligation on producers vs the legacy IH's `2 ≤ V(G').ncard` guard (they currently prove
`2 ≤`, will now prove `Nonempty`), and every IH target is nonempty by construction (cut
sides: explicit conjuncts of the L1e packaging; splits/contractions: `ncard ≥ 2` resp.
contains `r`). §1.56(c)'s draft IH (no guard) is unprovable as written — this is the
recorded flag doing its job, not a new gap. **(ii) the four-case split is KT p. 671
verbatim** (re-verified against the PDF this pass): ¬2EC (§6.1) / proper rigid subgraph
(§6.2) / 2EC + no-rigid + `k > 0` (§6.3) / 2EC + no-rigid + `k = 0` (§6.4), with IH (6.1)
over every nonnegative dof. `hcontract` carries **no** 2EC hypothesis — paper-faithful (KT's
§6.2 case never assumes it); the fact is available in the proof branch (the dispatch tests
2EC first), so adding it later would be a one-commit statement ripple if L5 ever surfaces a
need — it is *omitted* now because neither KT §6.2 nor the landed 22h `hcontract` arm
consumes it. **(iii) no `hD`, no `hfresh`, no `[Finite β]`** — the `_full` precedent: all
four `|V| ≥ 3` slots are handed the full conditioned IH ((β)-interface, §1.56(c)(iv)), so
the principle does no internal splitting/contracting and needs no combinatorial brick. The
only non-classical content is the `k`-dispatch: `0 ≤ k` from `hG.1 ▸ deficiency_nonneg G n
hne` (whence `by_cases hk : k = 0` gives `0 < k` in the negative branch via
`lt_of_le_of_ne` + `Ne.symm`) — that is what `[Finite α]` and the `Nonempty` hypothesis
feed. `[DecidableEq β]` rides on `IsMinimalKDof`. `TwoEdgeConnected` and the rigid-subgraph
existence dispatch by classical `by_cases`. **(iv)** `hsplitZero` is pinned at the
*instantiated* `IsMinimalKDof n 0` (no `k` binder + `hk : k = 0` equation), matching the
legacy `_full` `hsplit` slot shape its L7 producer restates from. **(v) proof skeleton:**
`intro k G; induction hN : V(G).ncard using Nat.strong_induction_on generalizing k G`
(the `_full` pattern + `k`); `ncard ≤ 2` → `hbase`; at `3 ≤ ncard` the three nested
`by_cases` per (ii)–(iii); IH plumbing `fun k' G' hG' hne' hlt => IH _ (hN ▸ hlt) k' G' rfl
hG' hne'`. One commit, no new lemma.

**(b) The slot-vs-inventory audit (all five clean against the landed Lean).**

| Slot | Discharging layer | Landed reduction brick(s) consumed there | Shape check |
|---|---|---|---|
| `hbase` | L3 | `isMinimalKDof_ncard_le_two_trichotomy` (Deficiency:2233) | slot supplies exactly its `hG`/`hne`/`hV ≤ 2`; producer adds its own `hD : 2 ≤ D` ✓ |
| `hcut` | L4 | `exists_cut_decomposition_of_not_twoEdgeConnected` (Deficiency:1507) | slot's `hntec` is its trigger; sides nonempty + `⊂ V(G)` (→ `ncard <` via `Set.ncard_lt_ncard`, `[Finite α]`) feed the guarded IH ✓ |
| `hcontract` | L5 | `rigidContract_isMinimalKDof` (Contraction:696, all-`k`) | slot's `∃ H` is its trigger; `[NeZero (bodyHingeMult n)]` from the producer's `hD`; smaller via `rigidContract_vertexSet_ncard_lt`, nonempty (contains `r`) ✓ |
| `hsplitPos` | L6 | `exists_degree_eq_two` (ReducibleVertex:673) + `splitOff_isMinimalKDof_of_pos` (ForestSurgery:3399) | slot supplies `htec`/`hnp`/`0 < k`/`3 ≤ ncard` — exactly their hypothesis sets minus the producer-side `hD : 3 ≤ D` and the fresh label (the producer carries its own `hfresh`, as `theorem_55_d3` already does; the principle has none) ✓ |
| `hsplitZero` | L7 (+L9 wiring) | the landed 22h Case-III chain, restated | strict superset of the legacy `_full` `hsplit` slot: gains `htec` (ignorable or consumed in place of `twoEdgeConnected_of_isKDof_zero`) and the **all-`k` IH** — the entire point (the `h622` derivation at the `k'`-dof `G_v`) ✓ |

**(c) The `k = 0` legacy arm: `minimal_kdof_reduction[_full]` stays, side by side.**
Neither wraps the other. The legacy is not derivable from the new principle (its `hbase` is
`ncard = 2` only and its motive contract is 0-dof-specific — instantiating `P' G :=
G.IsMinimalKDof n 0 → P G` strands the `ncard = 1` base case the legacy `hbase` never
covered); the new one is not derivable from the legacy (the legacy case lattice has no ¬2EC
case — at `k = 0` it is vacuous by `twoEdgeConnected_of_isKDof_zero` — and its IH is 0-dof-
only). `minimal_kdof_reduction` remains `thm:minimal-kdof-reduction`'s pin (KT Theorem 4.9,
a Phase-20 deliverable in its own right) and keeps its consumers until L9 re-pins the spine
onto the all-`k` principle; no deletion, no restate.

**(d) Blueprint disposition.** NEW node `thm:minimal-kdof-reduction-all-k`,
molecular-induction.tex `sec:molecular-induction-thm49`, directly after
`thm:minimal-kdof-reduction`; `\lean{Graph.minimal_kdof_reduction_all_k}` + `\leanok` in
the same L2 commit (green on landing); `\uses{def:k-dof, def:cut-edges-2ec,
def:rigid-subgraph}` (the principle's proof consumes only the case-split substrate — no
`lem:reduction-step*`, no `lem:reduction-measure`: it does no internal reduction).
Statement prose: this is **not a numbered KT theorem** — it is the induction skeleton of KT
Theorem 5.5's proof (the §6 opening, p. 671: the four-case split + IH (6.1)), stated as the
well-founded induction principle, citing \cite[Sect.~6]{katohTanigawa2011}; the existing
`thm:minimal-kdof-reduction` node gains nothing (its 0-dof statement is untouched). The L9
restate of `thm:theorem-55` will `\uses` the new node.

**(e) The L2 slice: one commit** — the Lean decl (ForestSurgery.lean beside
`minimal_kdof_reduction_full`) + the green blueprint node. Additive (no statement-grep
ripple). *Buildable.*

### 1.60 The L3 signature pin — the base producer (`hbase` carry): the genuine-hinge `|V| ≤ 2` base built on the landed trichotomy, the parallel-pair `k = 0` arm as the one new geometric brick (two non-proportional extensors inside a common panel `n^⊥`, fed to `theorem_55_base`), the rank conjunct closed by B1, re-aimed into `Pinning.lean`'s `theorem_55_base` as the rank engine; `theorem_55_base` is the *right* home but only as the LI-extensor-pair *engine* — the graph-level producer is NEW (2026-06-12)

> **Docs-only design pass (the L3 pin).** Lean read this pass (declarations, current line
> numbers, all verified this pass): CaseI.lean — `theorem_55_d3` (:6933, the `hbase`
> consumption: its current `hbase` slot is `∀ G, G.IsMinimalKDof n 0 → V(G).ncard = 2 →
> HasPanelRealization 2 n G` at :6936, threaded into `theorem_55_generic`'s `hbase` at :6977;
> its `hbaseGP` is discharged by vacuity via `not_simple_of_isMinimalKDof_of_ncard_two` at
> :6980); PanelHinge.lean — `HasPanelRealization` (M2, :1090), `theorem_55_generic` (:1168, the
> spine the L3 producer feeds, `hbase`/`hbaseGP` slots at :1169/:1171); `HasGenericFullRankRealization`
> (M3, :1035 — `IsGeneralPosition` + ℤ-rank + link-recording + `AlgebraicIndependent ℚ`);
> RigidityMatrix.lean — `ExtensorInPanel` (M1, :665), `BodyHingeFramework` (:684 — just
> `{graph, supportExtensor}`), `ofHinge` (:704); Pinning.lean — `theorem_55_base` (:630, the rank
> engine: `LinearIndependent ℝ ![supportExtensor e₁, supportExtensor e₂]` + two `IsLink _ u v` →
> `IsInfinitesimallyRigidOn {u,v}`), `eq_of_hingeConstraint_two_parallel` (the Lemma-5.3 leg it
> calls); GenericityDevice.lean — `isInfinitesimallyRigidOn_vertexSet_iff_finrank_span_rigidityRows`
> (B1, :532), `finrank_span_rigidityRows_add_deficiency_le` (B2, :562),
> `hasPanelRealization_of_generic` (M4, :1788); PanelLayer.lean — `exists_extensor_eq_panelSupportExtensor`
> (M1 engine, :453, only for *transversal* panels — degenerate at coincident panels, hence not the
> parallel-pair tool), `extensor_ne_zero_iff_linearIndependent` (Extensor.lean:270);
> Deficiency.lean — `isMinimalKDof_ncard_le_two_trichotomy` (:2233, landed L1b — the three
> disjuncts at :2236–:2239), `deficiency_of_edgeSet_empty` (:2023 — note `hne` dropped, gives
> `D(|V|−1)` for any `E = ∅`), `isKDof_zero_of_parallel_pair` (:606), `not_simple_of_isMinimalKDof_of_ncard_two`
> (ReducibleVertex.lean:768). KT 2011 read against the PDF this pass: p. 671 (the `|V| = 2`
> trichotomy (i) `E = ∅` / (ii) one edge / (iii) the parallel pair via Lemma 3.2; "(i) and (ii)
> are trivial"; Lemma 5.3's parallel-pair realization with `Π(u) = Π(v)` and `p(e) ≠ p(f)`,
> p. 669–670). Blueprint read: panel-layer.tex `def:genuine-hinge-realization` (:202, green),
> `lem:theorem-55-base` (:353, green), `thm:theorem-55-d3-instance` (:281, the `hbase` carry
> named at :316); deficiency.tex `lem:two-vertex-trichotomy` (:304, green). No `.lean`/`.tex`
> edits this pass.

**The corrected target shape (the §1.56(c) / carries-table fix the L2 floor flag forced).**
§1.56(c)/(d) and the carries table pinned `hbase` as "the `|V| = 2` trichotomy" re-aimed into
`theorem_55_base`. Two corrections fall out of reading the *landed* L2 principle (§1.59) and
`theorem_55_base` against the producer's actual obligation:

* **The slot is all-`k`, `Nonempty`, `ncard ≤ 2` — not `ncard = 2`, not 0-dof.** L2's `hbase`
  slot (§1.59(a)) is `∀ (k : ℤ) (G), G.IsMinimalKDof n k → V(G).Nonempty → V(G).ncard ≤ 2 → P G`.
  The current `theorem_55_d3`/`theorem_55_generic` `hbase` is the *legacy* 0-dof `ncard = 2`
  form (they run `minimal_kdof_reduction_full`, not yet the all-`k` principle). So the L3
  producer must cover **`ncard = 1` (`k = D·0 = 0`, `E = ∅`)** as well as the three `ncard = 2`
  arms — the floor flag's "covers `1 ≤ ncard ≤ 2`" is a real extra arm, not bookkeeping. At
  `P G = Pc G := (G.Simple → HasGenericFullRankRealization 2 n G) ∧ HasPanelRealization 2 n G`
  (the conditioned pair, §1.56(b) M4), the producer concludes the *pair*.
* **`theorem_55_base` is the right home but only as the LI-extensor-pair *engine*; the
  graph-level producer is NEW.** The carries table's "re-aim Pinning.lean's `theorem_55_base`"
  reads as if `theorem_55_base` *is* the base producer. It is not: it is a *framework-level* rank
  lemma (given a `BodyHingeFramework` whose two named edges carry LI supporting extensors,
  conclude `IsInfinitesimallyRigidOn {u,v}`). The L3 deliverable is the *graph-level* producer
  that (a) dispatches on the landed trichotomy, (b) for the parallel-pair arm *constructs* the
  framework with two LI extensors, (c) feeds `theorem_55_base`, (d) lifts its rigidity conclusion
  to the M2 rank conjunct via B1. `theorem_55_base` stays put in Pinning.lean (no re-aim needed —
  its `V(G)`-relative form already landed at Phase 21b); the new producer lives beside it.

**(a) The pinned graph-level base producer.** Pinning.lean, beside `theorem_55_base` (the file
that owns the rank engine; the producer is the base case of Theorem 5.5, so it sits with the
other Theorem-5.5-assembly lemmas there, not in CaseI.lean). One conditioned-pair producer:

```lean
/-- **Theorem 5.5 base producer** (`lem:theorem-55-base-producer`; `hbase` carry, Phase 22i L3).
The graph-level base case of the all-`k` reduction: a minimal `k`-dof-graph on `1 ≤ |V| ≤ 2`
bodies carries the conditioned realization pair. -/
theorem theorem_55_base_producer [DecidableEq β] [Finite α] [Finite β] {n : ℕ} {k : ℤ}
    (hD : 6 ≤ Graph.bodyBarDim n)
    (G : Graph α β) (hG : G.IsMinimalKDof n k)
    (hne : V(G).Nonempty) (hV : V(G).ncard ≤ 2) :
    (G.Simple → PanelHingeFramework.HasGenericFullRankRealization 2 n G) ∧
      HasPanelRealization 2 n G
```

Design notes:

* **`hD : 6 ≤ bodyBarDim n`** matches `theorem_55_d3`/`case_III_realization` (the `d = 3`,
  `D = 6 = screwDim 2` scope of all of 22i's producers; the `2 ≤ D` the trichotomy needs is a
  weakening). `k : ℤ` and the four typeclasses are exactly L2's `hbase` slot context (it carries
  `[DecidableEq β] [Finite α]`; `[Finite β]` rides on the trichotomy lemma). At the L9 spine the
  producer is applied with `k` from the principle's binder; for the *current* (legacy-spine)
  `theorem_55_d3` it is instantiated at `k = 0`, `hV : ncard = 2 → ncard ≤ 2` (`omega`) — so L3
  can also discharge `theorem_55_d3`'s present `hbase` slot in the same commit, by composing the
  producer's `.2` (the `HasPanelRealization` conjunct) — see (e).
* **The GP conjunct (`G.Simple → …`) must still be produced when `G.Simple` holds, but the
  parallel-pair arm is excluded by simplicity.** The landed `theorem_55_d3` discharges its
  `hbaseGP` (the `ncard = 2` GP case) by **vacuity** — a simple two-vertex minimal-0-dof graph
  does not exist (`not_simple_of_isMinimalKDof_of_ncard_two`, the parallel-pair arm is non-simple).
  At the all-`k` slot the producer must additionally handle `ncard = 1` and the simple `ncard = 2`
  *single-edge* arm. The GP arm by trichotomy (see (e) for the full statement): `ncard = 1` simple
  → `E = ∅`, target rank `0`, empty/single-body GP framework (rank 0, GP/link-recording vacuous,
  alg-indep of the one-body normal seed); `ncard = 2` simple → `|E| ≤ 1`, and `|E| = 1` (single
  edge, `k = 1`, `def = 1 > 0`) is *not* rigid, so its GP conjunct is a `def = 1` generic
  realization at rank `D − 1` — **a genuine GP construction, not vacuous**. This single-edge GP arm
  is the one place the GP conjunct does real work at the base, and is the reason the producer
  concludes the *pair*. *Flag (V-base):* a single edge gives only *one* nonzero extensor, rank
  `D − 1` (= target), so the single-edge arm uses the **single-row** rank fact, not `theorem_55_base`
  (which needs an LI extensor *pair* for full rank `D`); the rank conjunct closes by single-row-`≥`
  + B2-`≤` (see (c)/(d)).

**(b) The trichotomy dispatch (the bare `HasPanelRealization` conjunct).** `obtain` the landed
`isMinimalKDof_ncard_le_two_trichotomy (by omega : 2 ≤ D) hG hne hV`; three arms:

* **(i) `E(G) = ∅`, `k = D(|V|−1)` (covers `ncard ∈ {1, 2}`).** Target rank
  `D(|V|−1) − def = D(|V|−1) − k = 0` (`hG.1` pins `def = k`, the empty arm gives `k = D(|V|−1)`).
  Build `F := ⟨G, fun _ => 0⟩` (all-zero supportExtensor — every edge label, but `E = ∅` means no
  link fires the constraint). `rigidityRows = ∅` (no links), so `span = ⊥`, `finrank = 0`. M2
  conjuncts: `normal v := n₀` a fixed nonzero vector (panels nonzero); the per-link conjunct is
  **vacuous** (`E = ∅`, no `IsLink`); rank conjunct `0 = 0`. *Buildable*, no geometry.
* **(ii) single edge, `ncard = 2`, `k = 1`.** Target rank `D·1 − 1 = D − 1`. One genuine hinge:
  pick a nonzero `n` and build *one* extensor `C := extensor p₀` of two LI points `p₀ : Fin 2 →
  Fin 4 → ℝ` in `n^⊥` (the single-hinge analogue of (iii); the same `n^⊥`-point construction, one
  copy). `F := ⟨G, fun e' => if e' = e then C else 0⟩`. The single hinge-row block has rank
  `D − 1` (the landed single-row fact: one nonzero extensor constrains the relative screw to a
  `1`-codim subspace; `finrank (span {row}) = ` the row count of one `hingeRowBlock`, which is
  `D − 1` — *confirm the exact landed single-row rank lemma at the build, flag V-base*). M2: panels
  `normal u = normal v = n` (coincident, the parallel-pair carrier reason — but here a *single*
  edge, panels may as well coincide); `ExtensorInPanel C n` by the pointwise witness `⟨p₀, rfl, hperp⟩`;
  rank `= D − 1` by the single-row count `≥` and B2 `≤`. *Buildable from the single-row infra.*
* **(iii) parallel pair, `ncard = 2`, `k = 0` — THE NEW GEOMETRIC BRICK (KT Lemma 5.3, p. 670).**
  Target rank `D·1 − 0 = D` (full). Equal normals `n` at `u, v` (coincident panels); two
  *non-proportional* extensors `C_e, C_f`, each `extensor` of two points in `n^⊥`, with
  `LinearIndependent ℝ ![C_e, C_f]`. Build `F := ⟨G, fun e' => if e' = e then C_e else if e' = f
  then C_f else 0⟩`; feed `theorem_55_base huv hgen (hl_e) (hl_f)` (with `hgen : LinearIndependent
  ℝ ![F.supportExtensor e, F.supportExtensor f]` = the LI of `C_e, C_f` after `if`-reduction) to
  get `IsInfinitesimallyRigidOn {u,v}`; since `V(G) = {u,v}` (trichotomy), that is
  `IsInfinitesimallyRigidOn V(G)`, and **B1** (`isInfinitesimallyRigidOn_vertexSet_iff_finrank_span_rigidityRows`)
  turns it into `finrank (span rigidityRows) = D·(|V|−1) = D = target`. M2: panels `n ≠ 0`;
  `ExtensorInPanel C_e n ∧ ExtensorInPanel C_f n` by the two pointwise witnesses; rank by B1.
  *The one research-ish leaf of L3* — but de-risked: it is `theorem_55_base` (green) + B1 (green)
  + **the two-LI-extensors-in-`n^⊥` construction (NEW)**.

**(c) The new construction (the L3 substrate, the only genuinely new Lean): two non-proportional
`ScrewSpace 2` extensors inside a common hyperplane `n^⊥ ⊆ ℝ⁴`.** This is what (ii)/(iii) bottom
out on. Pin (pin-shape; checkdecls-gated at the build):

```lean
/-- For a nonzero `n : Fin 4 → ℝ`, there are two points-pairs in `n^⊥` whose extensors are
linearly independent. -/
theorem exists_linearIndependent_extensor_pair_perp {n : Fin 4 → ℝ} (hn : n ≠ 0) :
    ∃ (p q : Fin 2 → Fin 4 → ℝ),
      (∀ i, p i ⬝ᵥ n = 0) ∧ (∀ i, q i ⬝ᵥ n = 0) ∧
      LinearIndependent ℝ
        ![(⟨extensor p, extensor_mem_exteriorPower _⟩ : ScrewSpace 2),
          ⟨extensor q, extensor_mem_exteriorPower _⟩]
```

Design notes: **(i)** `n^⊥` is a 3-dim subspace of `ℝ⁴`; `⋀² n^⊥ ⊆ ⋀² ℝ⁴ = ScrewSpace 2` is
`(3 choose 2) = 3`-dimensional, so two LI decomposable elements exist with room to spare. The
clean route: pick three LI vectors `a, b, c` spanning `n^⊥` (from `n ≠ 0`, `finrank n^⊥ = 3`,
`exists_linearIndependent_of_le_finrank` — the same shape as `exists_two_perp_of_linearIndependent_normals`
at PanelLayer.lean:420, here for *one* normal not two), set `p := ![a, b]`, `q := ![a, c]`; then
`extensor p = a ∧ b`, `extensor q = a ∧ c`, and `a∧b, a∧c` are LI in `⋀²` iff `b, c` are LI mod
`⟨a⟩` — which holds since `a, b, c` are LI (standard: `extensor` of subfamilies of an LI family is
an LI family of extensors; **the load-bearing fact to locate/mirror at the build — flag V-base**:
`linearIndependent` of `![a∧b, a∧c]` from LI of `![a,b,c]`. mathlib's `ExteriorAlgebra`/`exteriorPower`
basis API or `Basis.tensorPower`-style results may give it; if not, a short project lemma in
Extensor.lean — it is the wedge analogue of "distinct 2-subsets of a basis give basis vectors of
`⋀²`"). **(ii)** the single-edge arm (ii) uses just the *first* pair `p` (one nonzero extensor;
`extensor_ne_zero_iff_linearIndependent` gives `C ≠ 0` from `a, b` LI). **(iii)** `n ≠ 0` comes
free from the producer's panel-normal choice (we *pick* `n`, e.g. `n := Pi.single 0 1`); it is not
extracted from `G`.

**(d) The rank conjunct closes uniformly by B1 (rigid arm) or single-row-`≥` + B2-`≤` (single
edge).** For (iii), B1 is an *equality* (`finrank = D(|V|−1)` ⟺ rigid-on-`V`), so the rigid
conclusion gives `= D` directly. For (ii) the framework is *not* rigid (`def = 1`), so B1 does not
apply; instead the single hinge-row gives the lower bound `finrank ≥ D − 1` (the row block has
that rank) and **B2** (`finrank_span_rigidityRows_add_deficiency_le`, with `hC : ∀ link, supportExtensor ≠ 0`
— the single edge's `C ≠ 0`) gives `finrank ≤ D·1 − def = D − 1`; antisymmetry closes the M2
equality. For (i) both sides are `0` (no rows). This is the §1.56(f) B2 role ("producers prove
`≥`, B2 closes `=`") at the base — B2 is already landed and `V(G)`-relative, no re-derivation.

**(e) The GP conjunct (`G.Simple → HasGenericFullRankRealization 2 n G`) at the base.** Cases on
the trichotomy under the extra `G.Simple`:

* parallel-pair arm (iii) is **excluded by `G.Simple`** (`e ≠ f` both linking `u,v` is a parallel
  pair, not simple) — `not_simple_of_isMinimalKDof_of_ncard_two` is the landed witness, exactly
  how `theorem_55_d3`'s `hbaseGP` is discharged today (vacuity);
* single-edge arm (ii) with `G.Simple`: this **does** occur (`def = 1 > 0`), and is the one base
  arm where the GP conjunct does real work — build the `PanelHingeFramework` `ofNormals` at a
  general-position alg-indep seed with the single edge's two distinct endpoints, GP forcing the
  single extensor nonzero, link-recording from `ofNormals`, alg-indep from the seed, rank `D − 1`
  via the single-row count. *Flag V-base:* this reuses the `case_*` `ofNormals`-at-alg-indep-seed
  pattern (the landed producers' standard opening) at the *single-row* count; confirm the landed
  single-row GP infra covers it, else it is a small new GP single-edge lemma;
* empty arm (i) with `G.Simple` (`ncard = 1`, `E = ∅`): GP framework is the single-body / empty
  framework, rank `0`, GP / link-recording vacuous, alg-indep of the one-body normal seed.

This is why the producer concludes the **pair** rather than `HasPanelRealization` alone (it feeds
the L9 spine's conditioned motive directly, mirroring `theorem_55_d3`'s `theorem_55_generic`
shape); and the bare `HasPanelRealization`-only legacy `hbase` slot of the *current*
`theorem_55_d3` is discharged in the same commit by `(theorem_55_base_producer hD G hG hne
(by omega)).2`, with `hne` from `ncard = 2`. The current `hbaseGP` slot stays its one-line vacuity
discharge (untouched) — or, if cleaner, is rewired to `(… ).1`; decide at the build.

**(f) Blueprint disposition.** `def:genuine-hinge-realization` (panel-layer.tex:202) and
`lem:theorem-55-base` (:353) are **already green** — L3 mints **one new node**
`lem:theorem-55-base-producer` in panel-layer.tex (directly after `lem:theorem-55-base`, before
`lem:theorem-55-triangle`), `\lean{…theorem_55_base_producer}` + `\leanok` on landing,
`\uses{lem:two-vertex-trichotomy, lem:theorem-55-base, lem:rank-parallel-full,
def:genuine-hinge-realization, def:rank-hypothesis}` (the trichotomy dispatch, the rank engine, the
parallel-hinges-full leg, the two motives). If the two-LI-extensors construction earns its own node
(it is a clean Grassmann fact), mint `lem:extensor-pair-in-panel` in extensor.tex or
rigidity-matrix.tex and `\uses` it; otherwise fold it into the producer's proof `\uses`. The
existing `thm:theorem-55-d3-instance` carries `hbase` as a named hypothesis (:316) — its
*statement* is unchanged at L3 (the carry is still threaded through `theorem_55_d3` until L9 rewires
the spine), so **no statement-grep ripple**; L3 only *adds* the producer node + green it. The
carry-discharge prose on `thm:theorem-55-d3-instance` is updated at **L9** (when the spine swaps to
the all-`k` principle and the carry physically disappears), not here — L3 lands the *tool* that L9
plugs in.

**(g) The L3 slice cut.** Two commits, the construction first (it is the only new math):

* **L3a** — `exists_linearIndependent_extensor_pair_perp` (+ the wedge-LI helper if needed) in
  Extensor.lean / PanelLayer.lean; the cheapest complete sub-step, gate-verified, no producer yet.
  Optionally mints `lem:extensor-pair-in-panel`.
* **L3b** — `theorem_55_base_producer` (the trichotomy dispatch + the three arms + the GP pair) in
  Pinning.lean, consuming L3a; the legacy-`hbase` rewire of `theorem_55_d3` in the same commit
  (additive, `.2`/`.1` projections); mints + greens `lem:theorem-55-base-producer`.

If L3a proves a one-lemma half-day (the wedge-LI fact is in mathlib), fold both into one commit;
if the wedge-LI fact needs a real Extensor.lean mirror, keep them split. *V-base* (the one
verification item L3 adds, resolve at the L3a/L3b design micro-pass before the first build):
the wedge-LI fact `LI ![a,b,c] → LI ![a∧b, a∧c]`, the landed single-hinge-row rank lemma name
(arm (ii)/(d)), and the single-edge GP infra (arm (ii)/(e)). All three are bounded; none is
research-shaped (the only nontrivial geometry, the LI extensor pair, is a basis-level Grassmann
fact, not a KT crux).

### 1.61 The L4 signature pin — Lemma 6.1, the cut-edge / not-2-edge-connected case (`hcut`): one graph-level producer concluding the conditioned pair `Pc`, consuming the L1e cut decomposition + the smaller-graph IH; V5 RESOLVED — the closing `≤` is free (B2, landed), the substance is the lower bound `≥`, established by a NEW vertex-disjoint block-rank-addition lemma (the project's fixed-seed route replaces KT's isometry); the disconnected/connected split of KT collapses into one `cutEdges.ncard ∈ {0,1}` arithmetic; sliced L4a (the block-rank-addition brick, bare conjunct) → L4b (the producer + GP conjunct) (2026-06-13)

> **Docs-only design pass (the L4 pin).** Lean read this pass (declarations, current line numbers,
> all verified this pass): Deficiency.lean — `exists_cut_decomposition_of_not_twoEdgeConnected`
> (:1507, the L1e opener: `hD : 1 ≤ bodyBarDim n`, `hG : IsMinimalKDof n k`, `hntec`; yields
> `V₁ k₁ k₂` with `V₁.Nonempty ∧ V₁ ⊂ V(G) ∧ (V(G) ∖ V₁).Nonempty ∧ (induce V₁).IsMinimalKDof n k₁
> ∧ (induce (V(G)∖V₁)).IsMinimalKDof n k₂ ∧ (cutEdges V₁).ncard ≤ 1 ∧ k = k₁ + k₂ + D − (D−1)·|cut|`),
> `cutEdges` (:851), `TwoEdgeConnected` (:859), `deficiency_eq_of_cutEdges_ncard_le_one` (the cut
> arithmetic L1e wraps); ForestSurgery.lean — `minimal_kdof_reduction_all_k` (the L2 principle, §1.59;
> the `hcut` slot at §1.59(a): `∀ (k : ℤ) (G), IsMinimalKDof n k → 3 ≤ ncard → ¬ TwoEdgeConnected →
> (guarded-IH) → P G`); PanelHinge.lean — `HasPanelRealization` (M2, :1090, the `{F, normal}` + nonzero
> panels + genuine/contained links + ℤ-rank conjunct), `HasGenericFullRankRealization` (M3, :1035),
> `theorem_55_generic` (:1168 — still the *legacy 0-dof* spine; the all-`k` spine `theorem_55_all_k` is
> L9, so the L4 producer has **no current consumer** — it stands alone until L9 wires the `hcut` slot);
> RigidityMatrix.lean — `BodyHingeFramework` (:684, just `{graph, supportExtensor}`),
> `rigidityRows` (:919, `{φ | ∃ e u v, IsLink e u v ∧ ∃ r ∈ hingeRowBlock e, φ = hingeRow u v r}`),
> `hingeRowBlock` (:753), `finrank_hingeRowBlock` (:1049, `= D−1`), `linearIndependent_hingeRow` (:902);
> Pinning.lean — `span_rigidityRows_eq_sup_span_panelRow_edge` (:343, the *single-deleted-edge, same
> vertex set* span split — the closest landed precedent, NOT the disjoint-sides one L4 needs),
> `exists_independent_panelRow_of_edge` (:403, the cut row's `D−1` independent rows),
> `finrank_span_panelRow_edge` (:305); GenericityDevice.lean — `…finrank_span_rigidityRows_add_deficiency_le`
> (B2, :562, the `V(G)`-relative `≤` upper bound — the closing half, free), B1 (:532, the rigid-iff,
> applies only at `def = 0`, NOT the cut case in general), `…finrank_span_rigidityRows_add_finrank_infinitesimalMotions`
> (the complement brick, :503). KT 2011 read against the PDF this pass: p. 671 (the §6 opening — IH (6.1)
> over every nonnegative `k_H`; the four-case `|V| ≥ 3` split), **p. 672 §6.1 Lemma 6.1 verbatim** (the
> cut-edge decomposition `k = k₁ + k₂ + 1` by Lemma 3.6, sides minimal `kᵢ`-dof by Lemma 3.3, the isometry
> making `ΠG₁,p₁(v₁)`/`ΠG₂,p₂(v₂)` nonparallel for *every* cross pair → `ΠG₁,p₁(u) ∩ ΠG₂,p₂(v)` a
> `(d−2)`-flat, `p(uv)` = that flat, the block-triangular rank addition over the single cut row
> `r(p(uv))` of rank `D−1` via Lemma 5.1 pin-a-body, "the disconnected case is proved in the same
> manner"). Blueprint read: molecular-induction.tex `thm:minimal-kdof-reduction-all-k` (:1269, green),
> deficiency.tex `lem:cut-edge-decomposition` (:179, green), panel-layer.tex
> `def:genuine-hinge-realization` (:201, green). No `.lean`/`.tex` edits this pass.

**Citation.** Katoh–Tanigawa 2011, *Discrete Comput. Geom.* **45**, 647–700; **Lemma 6.1**, §6.1, p. 672
(the not-2-edge-connected case of the all-`k` Theorem 5.5 induction). The cut decomposition `k = k₁ + k₂ + 1`
is KT's **Lemma 3.6** (deficiency over a cut, p. 658) + **Lemma 3.3** (sides minimal, p. 657); the cut-row
rank `D − 1` and the pin-a-body equality `rank R(G₁,p₁; E₁, V₁∖{u}) = rank R(G₁,p₁)` are **Lemma 5.1**
(p. 668, the [29] = Tay–Whiteley fact). All verified against the PDF this pass.

**Red-node consistency gate (run on the L4 inputs).** L4 *mints* its producer node — there is **no
existing cut-edge / Lemma-6.1 realization node** in the dep-graph (structural-edit mode: per-slice
restate, no new chapter). The two green nodes L4 consumes were re-read end-to-end: `lem:cut-edge-decomposition`
(deficiency.tex:179 — statement and proof both route through the Lemma-3.6 partition argument + Lemma-3.3
sides-minimal, unifying KT's connected/disconnected cases by `|cut| ∈ {0,1}`; no `\uses` at a superseded
node) and `thm:minimal-kdof-reduction-all-k` (molecular-induction.tex:1269 — the four-case skeleton, its
`hcut` slot is L4's exact obligation). `blueprint/lint.sh` green (supersession gate included). Both
self-consistent; the L4 producer plugs into the `hcut` slot at L9.

**The slot the producer fills.** L2's `hcut` slot (§1.59(a)), at `P G = Pc G :=
(G.Simple → HasGenericFullRankRealization 2 n G) ∧ HasPanelRealization 2 n G` (§1.56(b) M4):

```text
hcut : ∀ (k : ℤ) (G), G.IsMinimalKDof n k → 3 ≤ V(G).ncard → ¬ G.TwoEdgeConnected →
  (∀ (k' : ℤ) (G'), G'.IsMinimalKDof n k' → V(G').Nonempty → V(G').ncard < V(G).ncard → Pc G') →
  Pc G
```

So the producer receives `hG`, `3 ≤ ncard`, `hntec`, and the guarded conditioned IH; it must conclude
`Pc G`. Its first move is the L1e opener `exists_cut_decomposition_of_not_twoEdgeConnected (by omega : 1 ≤ D)
hG hntec`, yielding the cut `V₁`, side dofs `k₁ k₂`, the two minimal-dof induced sides, `|cutEdges V₁| ≤ 1`,
and the deficiency arithmetic `k = k₁ + k₂ + D − (D−1)·|cut|`. Both sides are nonempty and strictly smaller
(`V₁ ⊂ V(G)` and `(V(G)∖V₁) ⊂ V(G)`, `[Finite α]` → `Set.ncard_lt_ncard`), so the guarded IH applies to each.

**(a) V5 RESOLVED — the fixed-seed transversality route, and where the real work is.** The pin's central
finding: **the closing `≤` half is already free.** B2 (`finrank_span_rigidityRows_add_deficiency_le`, landed,
`V(G)`-relative) gives `(finrank (span F.rigidityRows) : ℤ) ≤ D(|V(G)|−1) − def(G̃)` for *any* body-hinge
`F` whose hinges are genuine on links (`hC`) and whose `bodyBarDim n = screwDim k`. So the entire L4
difficulty collapses onto the **lower bound** `finrank (span F.rigidityRows) ≥ D(|V|−1) − k`; antisymmetry
with B2 + `def(G̃) = k` (`hG.1`) closes the M2 equality. This is the same `≥`-then-B2 closing pattern §1.60(d)
pinned for the base producer's single-edge arm — B2 is the universal `≤`, the producer only ever supplies `≥`.

* *Why B1 does NOT apply.* B1 (the rigid-iff) is an *equality* only at `def = 0`. The cut case has
  `def(G̃) = k = k₁ + k₂ + 1 ≥ 1` (connected) or `k₁ + k₂ + D` (disconnected) — generally `> 0`, so the
  combined framework is **not** rigid-on-`V(G)` and B1 cannot supply the lower bound. The lower bound is
  KT's block-triangular rank addition, and it must be built (it is the substance of L4).

* *The project's fixed-seed route vs KT's isometry (§1.56(d)).* KT realizes the two sides at *independent*
  placements `p₁, p₂`, then applies an isometry to make `ΠG₁,p₁(v₁)` / `ΠG₂,p₂(v₂)` nonparallel for every
  cross pair, so the single cut hinge `p(uv) = ΠG₁,p₁(u) ∩ ΠG₂,p₂(v)` is a genuine `(d−2)`-flat. The
  project builds the **combined `BodyHingeFramework` directly on the shared `α`** (no re-homing — both IH
  side-frameworks already live over the same `α`; `BodyHingeFramework` is just `{graph, supportExtensor}`),
  by edge-label dispatch:
  ```text
  F := ⟨G, fun e => if e ∈ E(G.induce V₁) then F₁.supportExtensor e
                    else if e ∈ E(G.induce (V(G)∖V₁)) then F₂.supportExtensor e
                    else C_cut⟩          -- C_cut a genuine extensor in the common panel n_u^⊥ ∩ n_v^⊥
  ```
  For the **bare conjunct** the transversality KT engineers with the isometry **is not even needed**: any
  flat inside a common panel still has `C_cut ≠ 0` (the free-hinge carrier absorbs coincident panels — the
  same §1.56(a) freedom the parallel-pair base uses), and `ExtensorInPanel C_cut (normal u) ∧ ExtensorInPanel
  C_cut (normal v)` holds by construction (`C_cut` chosen in `n_u^⊥` resp. `n_v^⊥`, transversal or not). So
  V5's "transversality" is a **GP-conjunct-only** concern; the bare conjunct is transversality-free.

**(b) The lower bound — the NEW Lean (the block-rank-addition brick, the genuine L4 substrate).** The
`rigidityRows` of `F` decompose by edge over the three groups (`E₁`, the cut edge, `E₂`):
`span F.rigidityRows = span(R₁-rows) ⊔ span(cut-block) ⊔ span(R₂-rows)`, where `R_i-rows` are the rows
carried by `Eᵢ`-links (which equal `Fᵢ.rigidityRows` since `Fᵢ.supportExtensor = F.supportExtensor` on `Eᵢ`
and `G.induce Vᵢ` has exactly the `Eᵢ`-links). This is the multi-group analogue of the landed
single-edge split `span_rigidityRows_eq_sup_span_panelRow_edge` (Pinning.lean:343 — same proof shape,
`hsplit` now a three-way edge classification instead of two-way). The lower bound then needs the three
pieces **jointly independent enough**:
\[ \mathrm{finrank}(\mathrm{span}\,R_1 \sqcup \mathrm{cut} \sqcup \mathrm{span}\,R_2)
   \ge \mathrm{finrank}(R_1) + (D-1)\cdot|\mathrm{cut}| + \mathrm{finrank}(R_2). \]
The structural reason (KT's block-triangular matrix): `R₁`-rows are functionals of the screw assignment
that read only bodies in `V₁`, `R₂`-rows only bodies in `V₂`, and `V₁ ∩ V₂ = ∅` — so the three row-groups
act on **disjoint coordinate blocks** of `α → ScrewSpace k`. Concretely the brick to build (pin-shape,
checkdecls-gated at the build):

```lean
/-- **Vertex-disjoint block-rank addition** (`lem:rigidityRows-cut-rank-add`; KT Lemma 6.1 block-triangular
core; Phase 22i L4). For a body-hinge framework `F` whose link set partitions over a cut `V₁ ⊂ V(F.graph)`
with at most one crossing edge, the rigidity-row span's dimension is at least the sum of the two
side-spans plus the cut block. -/
theorem BodyHingeFramework.le_finrank_span_rigidityRows_of_cut [Finite α] [Finite β]
    (F : BodyHingeFramework k α β) {V₁ : Set α} (hcut : (F.graph.cutEdges V₁).ncard ≤ 1)
    (hC : ∀ e u v, F.graph.IsLink e u v → F.supportExtensor e ≠ 0)
    (… side/cut-edge classification hypotheses …) :
    Module.finrank ℝ (Submodule.span ℝ (F.restrictTo V₁).rigidityRows)
      + (screwDim k - 1) * (F.graph.cutEdges V₁).ncard
      + Module.finrank ℝ (Submodule.span ℝ (F.restrictTo (V(F.graph) ∖ V₁)).rigidityRows)
      ≤ Module.finrank ℝ (Submodule.span ℝ F.rigidityRows)
```
Design notes: **(i)** the disjoint-coordinate-block independence is the one genuinely new piece — express
each side's row span as the image of an injective coordinate-restriction map (`funLeft` to the side's
bodies; the dual-map injectivity precedent is `linearIndependent_hingeRow`/`hingeRow_funLeft_dualMap`,
RigidityMatrix.lean:865/902), so the two sides + cut land in a direct-sum-friendly position and
`Submodule.finrank_sup_add…`/`finrank_add_le_finrank_of_disjoint`-style additivity gives the `≥`. **(ii)**
the cut block is `(D−1)·|cut|`: zero rows in the disconnected case (`|cut| = 0`), `D−1` independent rows in
the connected case (`exists_independent_panelRow_of_edge` at the cut edge, `linearIndependent_hingeRow` lifting
the `(D−1)`-dim `hingeRowBlock` basis). **(iii)** `restrictTo Vᵢ` is the side framework `⟨G.induce Vᵢ,
F.supportExtensor⟩` (same extensors, induced graph) — its `rigidityRows` are exactly the `Eᵢ`-rows of `F`.
**(iv)** this is `buildable`, not research-shaped: it is KT's elementary block-triangular argument, the
disjoint-support refinement of the landed single-edge split. **Flag V5-a:** confirm at the build whether the
disjoint-block additivity lands cleanest via (route 1) the coordinate-restriction injection + a mathlib
`finrank` direct-sum lemma, or (route 2) the dual `infinitesimalMotions` side — `Z(G,p) ⊆ {S | S|_{V₁} ∈
Z(G₁,p₁) ∧ S|_{V₂} ∈ Z(G₂,p₂)}` plus the complement brick (the B1/B2 machinery is motion-side, so route 2
may reuse more). Route 1 is the primary; route 2 is the fallback if the row-side injection fights mathlib.

With the brick, the lower bound closes by arithmetic: the IH gives `finrank(Rᵢ) = D(|Vᵢ|−1) − kᵢ`
(`HasPanelRealization` conjunct of `Pc(G.induce Vᵢ)`), and `|V| = |V₁| + |V₂|` (`V₁ ⊔ (V(G)∖V₁)`), so
`finrank(R₁) + (D−1)|cut| + finrank(R₂) = D(|V₁|−1) − k₁ + (D−1)|cut| + D(|V₂|−1) − k₂
= D(|V|−1) − (k₁ + k₂ + D − (D−1)|cut|) = D(|V|−1) − k` (the L1e arithmetic, `omega`/`linarith` over ℤ).

**(c) The bare conjunct `HasPanelRealization 2 n G` (the L4a deliverable, transversality-free).** Assemble
`F` and `normal` (the panel assignment): take `normal v := F₁.normal v` for `v ∈ V₁`, `F₂.normal v` for
`v ∈ V(G)∖V₁` (both nonzero by the IH `HasPanelRealization` conjuncts; junk bodies off `V(G)` get a fixed
`n₀ ≠ 0`). Per-link conjunct: an `E₁`-link's extensor is `F₁`'s (nonzero + contained, from `Pc(G.induce V₁)`),
likewise `E₂`; the cut link's `C_cut ≠ 0` and `ExtensorInPanel C_cut (normal u) ∧ ExtensorInPanel C_cut
(normal v)` by the explicit construction (a genuine flat in `n_u^⊥ ∩ n_v^⊥`, or in each panel separately for
the bare conjunct — coincident-panel-tolerant). Rank conjunct: `≥` from the (b) brick + IH + L1e arithmetic,
`≤` from B2; antisymmetry. *Buildable from L4a + the IH + B2.*

**(d) The GP conjunct `G.Simple → HasGenericFullRankRealization 2 n G` (the L4b deliverable, where V5's
transversality genuinely bites — and the one OPEN sub-question to flag).** Under `G.Simple`, the induced
sides `G.induce Vᵢ` are simple (induced subgraphs of simple graphs are simple — fork has the instance), so the
IH delivers each side's GP conjunct `HasGenericFullRankRealization 2 n (G.induce Vᵢ)`. KT's conclusion is
"nonparallel if `G` is simple", which needs the cut hinge genuinely transversal (`p(uv)` a `(d−2)`-flat) and
the combined framework in general position. **The genuine open sub-question for the GP arm:** the two IH
side-frameworks are produced *each at its own independent alg-indep seed*; `HasGenericFullRankRealization`
carries an `AlgebraicIndependent ℚ` conjunct over the side's panel coordinates. Combining them into one GP
framework on `G` requires the *union* of the two seeds to be alg-independent, OR re-running both sides at one
shared global seed. Two candidate routes, **to adjudicate at the L4b design micro-pass before any GP build**:
* *Route GP-1 (fixed shared seed).* Re-run the IH at one global alg-indep seed shared across both sides
  (the project's "fixed-ambient-seed" style, §1.56(d)) — but the IH is a `Pc`-valued *hypothesis*, not a
  re-runnable producer, so this needs the IH's GP realization to be *re-seedable*, which it is not as a
  black box. Likely requires strengthening what the `hcut` slot's IH delivers (a seed-parametrized GP
  conjunct), a statement-level change — flag to coordinator.
* *Route GP-2 (independent-seed union).* Keep the two independent seeds and prove their union alg-independent
  (disjoint variable sets over `ℚ` → the union of two alg-indep families on disjoint index sets is alg-indep,
  a standard `MvPolynomial` fact — V5-b). Cross-side transversality then follows from general position at the
  combined seed. This is the route that matches "the choices of `p₁` and `p₂` are independent" (KT p. 672)
  and avoids re-seeding; it is the **recommended** route, but the alg-indep-of-disjoint-union lemma and the
  GP-forces-transversal step are unverified at this pass — **V5-b is the L4b open item.**

The bare conjunct (c) has **no such open question** — it is transversality-free and seed-free. This is why the
slice puts the bare conjunct first (L4a) and isolates the GP conjunct + its open sub-question in L4b.

**(e) Blueprint disposition.** L4 mints **one new node** `lem:case-cut-edge-realization` in molecular-induction.tex
(directly after `thm:minimal-kdof-reduction-all-k`, the principle whose `hcut` slot it fills) — *not* in the
algebraic-induction case chapters (it is a reduction-case producer, sibling to the all-`k` skeleton, and
consumes `lem:cut-edge-decomposition` from deficiency.tex). `\uses{lem:cut-edge-decomposition,
def:genuine-hinge-realization, def:rank-hypothesis, lem:rigidity-matrix-prop11-hub}` (B2's hub) plus the new
block-rank brick node if it earns one. If the (b) brick is a clean standalone Grassmann/linear-algebra fact,
mint `lem:rigidityRows-cut-rank-add` in rigidity-matrix.tex and `\uses` it; otherwise fold it into the
producer's proof `\uses`. No statement-grep ripple: the producer is additive (a new node), and the legacy
`theorem_55_d3` spine never reaches the cut case (0-dof is always 2EC), so nothing existing restates. The node
greens only when L4b lands the GP conjunct (the bare conjunct alone is green-modulo the GP arm — keep the node
red, or land it green-modulo with the GP conjunct carried as a tracked red sibling, per the L4 slice below).

**(f) The L4 slice cut.** Two layers, the bare conjunct first (it carries no open sub-question):

* **L4a** — `BodyHingeFramework.le_finrank_span_rigidityRows_of_cut` (the block-rank-addition brick, (b)) +
  the bare-conjunct producer concluding `HasPanelRealization 2 n G` for the `hcut` slot (the (c) assembly),
  in CaseI.lean or a new `CutEdge.lean` (decide at the build — it is a reduction-case producer; CaseI.lean
  is the precedent home for `theorem_55_d3`-adjacent producers, but a dedicated `CutEdge.lean` keeps the
  cut case isolated). Mints `lem:case-cut-edge-realization` (red, GP conjunct pending) + optionally
  `lem:rigidityRows-cut-rank-add`. The block-rank brick is the only genuinely-new math; the assembly is
  IH-plumbing + B2. **First concrete L4 commit.** *Buildable.*
* **L4b** — the GP conjunct `G.Simple → HasGenericFullRankRealization 2 n G`, after the L4b design
  micro-pass adjudicates Route GP-1 vs GP-2 + resolves V5-b (the alg-indep-of-disjoint-seed-union lemma).
  Greens `lem:case-cut-edge-realization` to the full pair. *Gated on the V5-b verdict — may need a
  statement-level IH change (Route GP-1) or a new `MvPolynomial` lemma (Route GP-2).*

*Verification items L4 adds:* **V5-a** (the disjoint-block additivity route — row-side injection vs
motion-side, (b)(iv); bounded, resolve at L4a's build); **V5-b** (the GP-conjunct seed-combination —
shared-reseed vs independent-union-alg-indep, (d); the one with real proof-shape uncertainty, resolve at the
L4b micro-pass before any GP build). V5-a is `buildable`; V5-b is the genuine open sub-question, isolated in
L4b and flagged to coordinator (it may force a statement-level change to what the `hcut` slot's IH delivers).

---

### 1.62 The L4b design micro-pass — V5-b RESOLVED: Route GP-2 is viable with NO IH statement-level change; the §1.61(d) "combine the two side seeds" framing rests on a false premise (both halves of it), and the project's actual GP route is the standing **fresh-shared-seed + rational-rank-polynomial non-root** idiom, generalized rigid→deficient by the already-landed W6e rank-input subfamily extractor; the one new project-internal piece is a deficiency-aware rank-polynomial extractor (a near-mechanical copy of `exists_rankPolynomial_of_rigidOn_linking`), no new `MvPolynomial` lemma (2026-06-13)

> **Docs-only design pass (the L4b V5-b adjudication).** Lean read this pass (declarations + current
> line numbers, all verified): PanelHinge.lean — `HasGenericFullRankRealization` (:1035, the GP motive:
> `∃ Q, Q.graph = G ∧ Q.IsGeneralPosition ∧ rank = D(|V|−1)−def ∧ link-recording ∧ AlgebraicIndependent ℚ
> (fun p : α × Fin (k+2) => Q.normal p.1 p.2)`), `IsGeneralPosition` (:121, `∀ a b, a ≠ b → LI ![normal a,
> normal b]` — a property of the *single combined* normal assignment on all of `α`), `theorem_55_generic`
> (:1168 — the `hcontractGP`/`hsplitGP` slots show the GP conjunct receives the *full conditioned IH*
> `∀ G', … → Pc G'`), `exists_generalPosition_polynomial` (:375, the rational GP factor, nonzero at any
> injective seed, whose non-root gives `IsGeneralPosition` of `ofNormals G ends q` for the *whole* graph),
> `ofNormals_endsOf_recordsLinks` (CaseI.lean:332, the link-recording term off the canonical selector);
> CaseI.lean — `hasGenericFullRankRealization_of_couple_ofNormals` (:158, the Case-I GP composer — the
> exemplar of the project's GP architecture: it does **not** combine the two leg seeds; it extracts each
> leg's *rational rank polynomial* from the leg's rigidity, builds one fresh seed `q₀ :=
> exists_injective_algebraicIndependent_real (α × Fin (k+2))`, proves `q₀` a simultaneous non-root of both
> + the GP factor, realizes at `q₀`, and reads `AlgebraicIndependent ℚ` straight off `halg q₀`),
> `case_cut_edge_realization` (:7588, the landed L4a bare conjunct — `F` assembled from the two IH
> `HasPanelRealization` side frameworks at their own seeds; seed-free brick + B2);
> GenericityDevice.lean — `exists_rankPolynomial_of_rigidOn_linking` (:1393, the rank-polynomial extractor,
> consumes `IsInfinitesimallyRigidOn V(G)` = rigidity = `def = 0`), `exists_independent_panelRow_subfamily_of_le_finrank`
> (:718, **W6e — the rigidity-FREE, rank-input subfamily extractor**: takes only `N ≤ finrank (span
> F.rigidityRows)` and yields `N` independent *linking* `panelRow`s; spans-the-rigidity-rows step needs only
> `hends`/transversality, no rigidity), `finrank_span_rigidityRows_add_deficiency_le` (:562, B2, the free
> `V(G)`-relative `≤`); Rank.lean — `exists_polynomial_ne_zero_of_linearIndependent_at_coeffs_subset_range`
> (:588, **the seed-transfer engine**: takes ANY linearly-independent panel-row subfamily at a source seed
> `p₀` and returns a *rational* `Q` with `eval p₀ Q ≠ 0` whose non-vanishing forces that same subfamily
> independent at any other seed — rigidity-free), `exists_injective_algebraicIndependent_real`
> (TranscendenceBasis.lean:70, the fresh single combined seed `q : σ → ℝ`, injective + `AlgebraicIndependent ℚ`);
> RigidityMatrix.lean — `le_finrank_span_rigidityRows_of_cut` (:2991, the L4a brick — **seed-free**:
> consumes only `F : BodyHingeFramework`, the cut structure, `hC_ext : ∀ e u v, IsLink → supportExtensor ≠ 0`);
> Deficiency.lean — `loopless_of_isMinimalKDof` (:370, every minimal-`k`-dof graph is loopless, so links
> join distinct bodies). Mathlib read via the Lean LSP MCP (`lean_loogle "AlgebraicIndependent _ (Sum.elim _ _)"`):
> `AlgebraicIndependent.sumElim` / `.sumElim_iff` (`Mathlib.RingTheory.AlgebraicIndependent.Transcendental`)
> — the *only* disjoint-index alg-indep facts upstream, and they require `AlgebraicIndependent
> (Algebra.adjoin R (Set.range x)) y` (the second family alg-indep over the field *extended by the first*),
> **NOT** the unconditional "disjoint variable sets → union independent" that the §1.61(d) GP-2 framing assumed.
> KT 2011 re-read against the PDF this pass: **p. 671** (the IH (6.1): "(nonparallel, if `Gₕ` is simple)
> … `rank R(Gₕ,pₕ) = D(|Vₕ|−1) − kₕ`" — the GP conjunct *and* the rank equality at the side's own placement),
> **p. 672 §6.1 Lemma 6.1 verbatim** ("the choices of `p₁` and `p₂` are independent of each other and …
> the rank … is invariant under an isometric transformation … we can take `p₁` and `p₂` such that
> `ΠG₁,p₁(v₁)` and `ΠG₂,p₂(v₂)` are nonparallel for any pair", `p(uv) = ΠG₁,p₁(u) ∩ ΠG₂,p₂(v)` a `(d−2)`-flat,
> `rank r(p(uv)) = D−1`, the block-triangular `rank ≥ …`). No `.lean`/`.tex` edits this pass.

**Citation.** Katoh–Tanigawa 2011, *Discrete Comput. Geom.* **45**, 647–700; **Lemma 6.1**, §6.1, p. 672,
and the §6 IH (6.1), p. 671. The transcendence-seed device (algebraically-independent-over-`ℚ` coordinates
as the standing inductive genericity choice) is KT's footnote 6, p. 685 — the project's realization of
"the choices of `p₁` and `p₂` are independent."

**(a) The §1.61(d) framing was wrong — both routes rested on a false premise.** §1.61(d) framed V5-b as
"the two IH side-frameworks are produced *each at its own independent alg-indep seed* … combining them into
one GP framework on `G` requires the *union* of the two seeds to be alg-independent, OR re-running both sides
at one shared global seed." Reading the *landed* GP architecture (`hasGenericFullRankRealization_of_couple_ofNormals`,
the only existing producer that lands the GP conjunct from two GP legs) refutes both halves:

* **The project never combines the IH seeds.** The Case-I GP composer does *not* touch either leg's seed. It
  extracts each leg's **rational rank polynomial** (a `Q : MvPolynomial (α × Fin (k+2)) ℝ` with `Q.coeffs ⊆
  range (algebraMap ℚ ℝ)`, nonzero at the leg's seed, whose non-vanishing forces the leg's rank), builds **one
  fresh combined seed** `q₀ := exists_injective_algebraicIndependent_real (α × Fin (k+2))` over *all* of `α ×
  Fin (k+2)`, proves `q₀` is a simultaneous non-root of `Q₁ · Q₂ · Q_gp` (the alg-indep seed is a non-root of
  every nonzero rational polynomial, `eval_ne_zero_of_coeffs_subset_range_of_algebraicIndependent`), and
  realizes `ofNormals G G.endsOf q₀` at that single seed. The motive's `AlgebraicIndependent ℚ` conjunct is then
  `halg` for `q₀` *directly*. So "Route GP-1 (reseed)" is a non-problem (there is nothing to reseed — the
  producer builds its own fresh seed) and "Route GP-2 (seed union)" mis-describes the mechanism.
* **The naive "GP-2 disjoint-union" fact is false anyway.** The only upstream disjoint-index alg-indep lemma
  is `AlgebraicIndependent.sumElim_iff`, which needs the *second* family alg-indep over `Algebra.adjoin ℚ
  (range first)` — not the unconditional "disjoint variable sets → union independent." Two independently-chosen
  transcendence-basis fragments of `ℝ/ℚ` are concrete reals and need *not* be jointly independent (one could be
  algebraic over the other). So even the seed-union route §1.61(d) called "recommended" would have been
  **unsound** as stated. This is why the project's idiom builds *one* fresh seed instead of merging two.

**(b) The genuine V5-b question, restated correctly, and its resolution (Route GP-2, viable, no IH change).**
The real obstruction is **not** seed-combination; it is **rank-lower-bound transfer across seeds for the
*deficient* (non-rigid) sides.** The combined GP producer builds one fresh seed `q₀` and needs the side rank
lower bound `finrank (span (⟨G.induce Vᵢ, ofNormals-extensors⟩).rigidityRows) ≥ D(|Vᵢ|−1) − kᵢ` *at* `q₀`. The
IH gives this equality only at the side's *own* seed. The existing transfer machinery
(`exists_rankPolynomial_of_rigidOn_linking`) consumes **rigidity** (`IsInfinitesimallyRigidOn V(G)`, i.e.
`def = 0`) — but the cut sides are general `kᵢ`-dof (`def = kᵢ`, possibly `> 0`), so they are **not rigid**, and
that extractor does not apply. *This* is V5-b's real content.

It resolves with already-landed infrastructure, because rigidity was only ever used to compute a *full-size*
`D(|V|−1)` independent subfamily. The Phase-22h **W6e** lemma `exists_independent_panelRow_subfamily_of_le_finrank`
is the rigidity-FREE generalization: given *only* `N ≤ finrank (span F.rigidityRows)`, it extracts `N`
independent *linking* `panelRow`s (the "span the rigidity rows" step needs only `hends`/transversality, no
rigidity). So the deficiency-aware transfer is:
1. From the side IH GP framework `Qᵢ` (at its own seed `qᵢ`): the rank equality gives `Nᵢ := D(|Vᵢ|−1) − kᵢ ≤
   finrank (span (Qᵢ.toBodyHinge).rigidityRows)`. Feed `Nᵢ` to **W6e** → `Nᵢ` independent linking `panelRow`s at `qᵢ`.
2. Feed that LI subfamily to the **seed-transfer engine**
   `exists_polynomial_ne_zero_of_linearIndependent_at_coeffs_subset_range` (rigidity-free; same `g`/`c`/`φ`
   Gram-minor coordinatization as `exists_rankPolynomial_of_rigidOn_linking`) → a *rational* `Qᵢ_rank` with
   `eval qᵢ Qᵢ_rank ≠ 0`, whose non-vanishing forces that subfamily (hence `rank ≥ Nᵢ`) at any seed.
3. Build the fresh combined seed `q₀`, a simultaneous non-root of `Q₁_rank · Q₂_rank · Q_gp` (alg-indep ⇒
   non-root of every nonzero rational poly). At `q₀`: each side has `rank ≥ Nᵢ`, the whole framework is in
   general position.

**The cross-side transversality KT engineers with the isometry is automatic from global GP at `q₀`.** Under
`IsGeneralPosition` (every pair of *distinct* bodies has independent normals) and `V₁ ∩ V₂ = ∅`, the cut
edge's endpoints `u_c ∈ V₁`, `v_c ∈ V₂` are distinct, so `supportExtensor_ne_zero_of_isGeneralPosition` makes
the cut hinge's extensor nonzero — the project's `(d−2)`-flat-transversal analogue, holding for *every* cross
pair at once (a strictly cleaner property than KT's per-pair isometry). Looplessness
(`loopless_of_isMinimalKDof`) gives the same for the two side blocks' edges. So the seed-free L4a brick's
hypothesis `hC_ext : ∀ e u v, IsLink → supportExtensor ≠ 0` is discharged on *all* edges by GP at `q₀`, and the
brick gives the combined lower bound `finrank (span F.rigidityRows) ≥ rank₁ + (D−1)|cut| + rank₂ ≥ D(|V|−1) − k`
by the L1e arithmetic `k = k₁ + k₂ + D − (D−1)|cut|` + `|V| = |V₁| + |V₂|` (identical to L4a's). B2 gives the
matching `≤`; antisymmetry closes the rank equality. **Verdict: Route GP-2 (independent placements, one fresh
combined non-root seed, per-side rank transfer) is viable and needs NO IH statement-level change.** The decision
guard's GP-1 escape (a seed-parametrized IH GP conjunct) is **not** triggered.

**(c) V5-b — the one new piece (no new `MvPolynomial` lemma).** The disjoint-union alg-indep lemma §1.61(d)
hoped for is *not needed and would be unsound*; `exists_injective_algebraicIndependent_real` already supplies the
single fresh seed. The one genuinely-new declaration is a **deficiency-aware rank-polynomial extractor**, the
non-rigid sibling of `exists_rankPolynomial_of_rigidOn_linking`:

```lean
/-- **Rank-input rank polynomial** (Phase 22i L4b; the deficiency-aware sibling of
`exists_rankPolynomial_of_rigidOn_linking`). A framework with a rank LOWER BOUND `N` on its
rigidity-row span yields a nonzero rational polynomial `Q` whose non-vanishing forces `N`
independent linking panel rows (hence `rank ≥ N`) at *any* seed. No rigidity. -/
theorem PanelHingeFramework.exists_rankPolynomial_of_le_finrank_linking [Finite α] [Finite β]
    (G : Graph α β) (ends : β → α × α)
    (hends : ∀ e u v, G.IsLink e u v → G.IsLink e (ends e).1 (ends e).2)
    {q₀ : α × Fin (k + 2) → ℝ}
    (hne : ∀ e, G.IsLink e (ends e).1 (ends e).2 →
      (ofNormals G ends q₀).toBodyHinge.supportExtensor e ≠ 0)
    {N : ℕ} (hN : N ≤ Module.finrank ℝ (Submodule.span ℝ (ofNormals G ends q₀).toBodyHinge.rigidityRows)) :
    ∃ Q : MvPolynomial (α × Fin (k + 2)) ℝ,
      MvPolynomial.eval q₀ Q ≠ 0 ∧ (Q.coeffs : Set ℝ) ⊆ Set.range (algebraMap ℚ ℝ) ∧
      ∀ q, MvPolynomial.eval q Q ≠ 0 →
        N ≤ Module.finrank ℝ (Submodule.span ℝ (ofNormals G ends q).toBodyHinge.rigidityRows)
```
Its proof is the existing `exists_rankPolynomial_of_rigidOn_linking` with two swaps: (i) replace the
rigid subfamily extractor `exists_independent_panelRow_subfamily_of_rigidOn_linking` by the rank-input
**W6e** `exists_independent_panelRow_subfamily_of_le_finrank` (feeding `hN`); (ii) re-phrase the conclusion
from "rows linearly independent" to "rank ≥ N" via `LinearIndependent.le_finrank_span` /
`finrank_span_le_of_...` on the `N`-element subfamily plus `span_panelRow_linking_eq_rigidityRows`. The
`g`/`c`/`φ` Gram-minor coordinatization and the rational-coefficient bookkeeping are copied verbatim. This is
`buildable`, not research-shaped.

**(d) The GP-conjunct producer signature, and how it composes with the landed bare conjunct.** The slot is
`Pc G = (G.Simple → HasGenericFullRankRealization 2 n G) ∧ HasPanelRealization 2 n G` (§1.56(b) M4). The full
slot-filler is `⟨gp, bare⟩` where `bare` is the **landed** `case_cut_edge_realization` (the `.2` conjunct,
unchanged — its IH is the `.2` projection of the conditioned IH) and `gp` is the new L4b producer (the `.1`
conjunct, fed the *full* conditioned IH so it can extract each side's GP realization, mirroring `hcontractGP`):

```lean
theorem case_cut_edge_realization_gp [DecidableEq β] [Finite α] [Finite β] {n : ℕ}
    (hD : 2 ≤ Graph.bodyBarDim n) (hn : Graph.bodyBarDim n = screwDim 2)
    {k : ℤ} (G : Graph α β) (hG : G.IsMinimalKDof n k) (_hV3 : 3 ≤ V(G).ncard)
    (hntec : ¬ G.TwoEdgeConnected) (hSimple : G.Simple)
    (hIH : ∀ (k' : ℤ) (G' : Graph α β), G'.IsMinimalKDof n k' → V(G').Nonempty →
      V(G').ncard < V(G).ncard →
      (G'.Simple → PanelHingeFramework.HasGenericFullRankRealization 2 n G') ∧
        HasPanelRealization 2 n G') :
    PanelHingeFramework.HasGenericFullRankRealization 2 n G
```
Body: cut decomposition (L1e, as L4a); each side `G.induce Vᵢ` is simple (induced subgraph of a simple graph;
fork has the `Simple.induce` instance) so `(hIH kᵢ (G.induce Vᵢ) … ).1 hSimpleᵢ` gives the side GP framework
`Qᵢ`; per-side W6e + `exists_rankPolynomial_of_le_finrank_linking` → `Qᵢ_rank`; `exists_generalPosition_polynomial
G G.endsOf` → `Q_gp`; one fresh `q₀` non-root of the triple (`exists_injective_algebraicIndependent_real` +
`eval_ne_zero_of_coeffs_subset_range_of_algebraicIndependent` thrice); set `Q := ofNormals G G.endsOf q₀`,
`F := Q.toBodyHinge`; GP from `Q_gp` non-root; side ranks `≥ Nᵢ` at `q₀` from the transfer polys + the
side-span equalities of L4a (`hF₁span`/`hF₂span`, reused — the `ofNormals`-on-`G.induce Vᵢ` rows equal `F`'s
`Eᵢ`-rows); combined `≥ D(|V|−1)−k` from the **seed-free L4a brick** + L1e arithmetic; `≤` from B2; antisymmetry;
link-recording from `ofNormals_endsOf_recordsLinks`; `AlgebraicIndependent ℚ` from `halg`. *Buildable* once
`exists_rankPolynomial_of_le_finrank_linking` lands.

**(e) Blueprint disposition (settles §1.61(e)).** Keep the **green-bare + restate-to-`Pc`** structure §1.61(e)
sketched, concretely: `lem:case-cut-edge-realization` (molecular-induction.tex) stays **green at the bare
`HasPanelRealization` conjunct** — its role-prose already says so (the 0dd8b09 repair). L4b mints **one new
node** `lem:case-cut-edge-realization-gp` for the `G.Simple → HasGenericFullRankRealization` conjunct, `\uses`-ing
`lem:case-cut-edge-realization` (bare), `lem:rigidityRows-cut-rank-add` (the seed-free brick),
`def:rank-hypothesis`, `prop:rigidity-matrix-prop11` (B2's hub), the GP-device nodes (the rank-polynomial /
seed-transfer / general-position-factor chain the Case-I GP composer already `\uses`), and a small new node
`lem:rank-polynomial-of-le-finrank` for the deficiency-aware extractor (c) if it earns one (else fold into the
producer's `\uses`). The L9 spine consumes the conjunction `⟨gp, bare⟩` at the `hcut` slot. This is the
restate-as-a-sibling option (not a single restated node), chosen because the bare conjunct is already green and
seed-free while the GP conjunct is seed-and-transversality-bearing — splitting keeps the green honesty gate
honest and matches how `theorem_55_generic` keeps `hsplit`/`hsplitGP` (bare/GP) as *separate* slots. No
statement-grep ripple (both nodes additive; the legacy `theorem_55_d3` spine never reaches the cut case).

**(f) The L4b slice cut (exact-signature build leaves, build order).**

* **L4b-1** — `PanelHingeFramework.exists_rankPolynomial_of_le_finrank_linking` (the deficiency-aware
  rank-polynomial extractor, (c)) in GenericityDevice.lean, beside `exists_rankPolynomial_of_rigidOn_linking`.
  The only genuinely-new declaration; a two-swap copy of its rigid sibling. Mints (optionally)
  `lem:rank-polynomial-of-le-finrank`. **First concrete L4b commit.** *Buildable.*
* **L4b-2** — `case_cut_edge_realization_gp` (the GP-conjunct producer, (d)) in CaseI.lean, beside
  `case_cut_edge_realization`. Composes L4b-1 + the side IH GP frameworks + the fresh-seed device + the seed-free
  L4a brick + B2; reuses L4a's `hF₁span`/`hF₂span`/arithmetic. Greens `lem:case-cut-edge-realization-gp`;
  completes the full `Pc` slot-filler `⟨gp, bare⟩` for the `hcut` slot. *Buildable on L4b-1.*

*Verification items L4b resolves:* **V5-b** (the GP-conjunct seed question) — **RESOLVED** as a rank-transfer
question (not a seed-combination one); Route GP-2 viable, no IH change, no new `MvPolynomial` lemma; the one new
piece is the deficiency-aware extractor (c). No residual open sub-question for L4b.

---

### 1.63 The L5 signature pin — Lemma 6.2, the non-simple Case-I branch (`hcontract`): the `hcontract` slot is a `by_cases` dispatch on `G.Simple` (the §1.55(c) precedent generalized to all-`k`), simple → forgetful M4 ∘ the all-`k`-restated GP `case_I_realization` (6.5 sub-arm carried as `h65`, L8), non-simple → the NEW KT Lemma 6.2 coincident-panel splice; V6 RESOLVED — the landed N6a `hasFullRankRealization_of_splice_of_supportExtensor` cannot be re-aimed (it concludes the *deleted* `HasFullRankRealization` and is `PanelHingeFramework`/`ofNormals`-bound), so L5's non-simple branch is a fresh `BodyHingeFramework`-native bare producer mirroring the landed L4a `case_cut_edge_realization` shape, with the coincident-panel cut hinge supplied by the already-landed `exists_extensor_in_two_panels` (which works AT `n=n`); sliced L5a (the non-simple bare producer) → L5b (the simple-branch all-`k` GP restate + the dispatch) (2026-06-13)

> ⚠️ **(c)/(f) SUPERSEDED by §1.64 (2026-06-13, the L5a-i boundary pair + the L5a re-pin).** The splice-brick
> statement and slice in (c)/(f) below are **WRONG** — read §1.64 for the corrected pin; the text is kept here
> only because the surrounding (a)/(b)/(d)/(e) of §1.63 still stand and §1.64 cites them. The error: the
> contraction leg was stated as `induce ((V(G)∖V(H))∪{r})` and framed as a *bare, transversality-free*
> block-triangular brick, but `rigidContract G H r = (G ＼ E(H)).map (collapseTo r V(H))` *collapses* V(H)→r —
> same vertex set as `induce`, but it **keeps the relabelled crossing edges** `induce` drops, so the
> induce-leg rank `≠ D(|V|−2)−k` (a strictly weaker bound the producer can't close), and the IH supplies the
> *contraction's* (`rigidContract`'s) realization, not the induce-leg's. §1.64 replaces (c)'s brick + (f)'s
> slice; the (a) dispatch, (b) V6 (N6a dead infrastructure), and (d) L5b simple-branch restate verdicts
> **stand unchanged**. (The bare `induce`-brick was built — sonnet primary 90e8d4a — and reverted.)

> **Docs-only design pass (the L5 pin).** Lean read this pass (declarations + current line numbers, all
> verified this pass): GenericityDevice.lean — `hasFullRankRealization_of_splice_of_supportExtensor` (:915,
> N6a, the bare splice; **concludes `PanelHingeFramework.HasFullRankRealization k G`** — the M5-deleted weak
> motive — with `hends : ∀ e, G.IsLink e (ends e).1 (ends e).2` and `hsupp : ∀ e, (ofNormals G ends
> q₀).toBodyHinge.supportExtensor e ≠ 0` quantified over ALL `e : β`, the two legs as `withGraph GH`/`withGraph
> Gc` of the *parent* `ofNormals G ends q₀`, rigid on `V(GH)`/`V(Gc)`), `…_of_supportExtensor_ofNormals` (:1095,
> the leg-native bare variant — same `HasFullRankRealization` conclusion, legs as `ofNormals GH/Gc ends q₀`),
> `hasGenericFullRankRealization_of_splice_ofNormals` (:1045, the GP splice, concludes the *legacy* M3 shape
> with `hdef : G.deficiency n = 0`), `hasPanelRealization_of_generic` (:1903, M4 forgetful: `[G.Loopless]`,
> `2 ≤ V(G).ncard`, `HasGenericFullRankRealization 2 n G → HasPanelRealization 2 n G`),
> `finrank_span_rigidityRows_add_deficiency_le` (:562, B2, the free `V(G)`-relative `≤`); CaseI.lean —
> `case_I_realization` (:2155 — `{n k : ℕ}`, `hD : 3 ≤ bodyBarDim n`, `hG : G.IsMinimalKDof n 0`, `{H} hH :
> IsProperRigidSubgraph`, `{r} hr : r ∈ V(H)`, `hVH2 : 2 ≤ V(H).ncard`, `hSimple : G.Simple`, **`hcSimple :
> (G.rigidContract H r).Simple`**, conditioned `hIH` over `IsMinimalKDof n 0`/`2 ≤ ncard`; concludes
> `HasGenericFullRankRealization k n G` — the **simple-and-simple-contraction Lemma-6.3 arm only**, NOT the 6.5
> arm), `couple_geometry_of_isProperRigidSubgraph` (:560 — yields `H ≤ G`, `G.deleteEdges E(H) ≤ G`, `r ∈ V(H)`,
> `r ∈ V(G ＼ E(H))`, the cover, both nonempty), `case_cut_edge_realization` (:7588, the landed L4a *bare* all-`k`
> producer — `{k : ℤ}`, `IsMinimalKDof n k`, `.2`-projected IH, concludes `HasPanelRealization 2 n G`; the L5a
> shape precedent), `case_cut_edge_realization_gp` (:7979, the landed L4b GP producer — full conditioned IH;
> the L5b shape precedent); PanelHinge.lean — `HasPanelRealization` (M2, :1090), `HasGenericFullRankRealization`
> (M3, :1035), `theorem_55_generic` (:1168 — the *legacy 0-dof* spine, `hcontract`/`hcontractGP` slots at
> :1185/:1190; the all-`k` spine `theorem_55_all_k` is L9 and **does not yet exist**, so the L5 producer stands
> alone until L9 wires the `hcontract` slot — confirmed by grep, exactly the L4 situation), the `hcontractGP`
> slot lambda (:1212, `fun … hrig hSimple hIH => ⟨fun hSimple => hcontractGP …, hcontract …⟩`); Deficiency.lean —
> `isKDof_zero_of_parallel_pair` (:606 — a two-vertex two-parallel-edge multigraph is `0`-dof for `D ≥ 2`),
> `IsProperRigidSubgraph` (:428, the G5-repaired `2 ≤ V(H).ncard` is `.2.1`), `loopless_of_isMinimalKDof`
> (:370); ReducibleVertex.lean — `simple_of_isMinimalKDof_of_noRigid` (:625, G0); Contraction.lean —
> `rigidContract_isMinimalKDof` (:696, **the N4 bridge IS all-`k`: `{k : ℤ}`, `IsMinimalKDof n k →
> IsProperRigidSubgraph → (G.rigidContract H r).IsMinimalKDof n k`** — V4 already discharged in the landed Lean,
> no generalization needed), `rigidContract_simple` (:144 — conditional on `hloop`/`hpar`, NOT derivable from
> `IsProperRigidSubgraph + G.Simple`; KT takes `G/E'` simple as a *case hypothesis*); PanelLayer.lean —
> `exists_extensor_in_two_panels` (:631 — **the coincident-panel construction: a nonzero `C : ScrewSpace 2`
> with `ExtensorInPanel C n₁ ∧ ExtensorInPanel C n₂` for ANY `n₁ n₂`, including `n₁ = n₂`** — built for L4a's cut
> hinge, exactly the genuine-`(d−2)`-flat-in-a-common-panel KT 6.2 needs). KT 2011 read **against the PDF this
> pass** (offset `printed p.N = pdf page (N − 647)`): **p. 673 §6.2 Lemma 6.2 verbatim** (proof sketch: `G' =
> (V', E')` proper rigid in minimal `k`-dof `G`, `G'` minimal-`0`-dof with `1 < |V'| < |V|` by Lemma 3.3, `G/E'`
> minimal-`k`-dof with `|(V∖V')∪{v*}| < |V|` by Lemma 3.5; IH gives `(G', p₁)` at `rank D(|V'|−1)` and
> `(G/E', p₂)` at `rank D(|V∖V'∪{v*}|−1) − k`; "replace the body associated with `v*` by `(G', p₁)`"; **Lemma
> 6.2 statement** = "minimal `k`-dof, `|V| ≥ 3`, NOT simple, (6.1) ⟹ a panel-hinge realization at `rank
> R(G,p) = D(|V|−1) − k`"; **proof**: `e, f` multiple edges joining `a, b`; `G[{e,f}]` is a proper rigid
> subgraph since `ẽ ∪ f̃` carries `D` edge-disjoint spanning trees on `{a,b}`; take `G' = G[{e,f}] = (V'={a,b},
> E'={e,f})`; **Lemma 5.3** gives `(G', p₁)` with `rank R(G',p₁) = D` and **coincident panels** `Π_{G',p₁}(a) =
> Π_{G',p₁}(b)`; (6.1) gives `(G/E', p₂)` at `rank R(G/E',p₂) = D(|V|−2) − k`; "since the choices of `p₁` and
> `p₂` are independent" take `Π_{G/E',p₂}(v*) = Π_{G',p₁}(a) = Π_{G',p₁}(b)` — **the coincident-panel splice at
> the contraction's panel**; (6.2) the spliced map `p|E' = p₁`, `p|E∖E' = p₂`; (6.3) the block-triangular matrix
> `[[R(G',p₁), 0],[∗, R(G,p;E∖E',V∖V')]]`), **p. 674** (the rank chain: (6.4)/(6.5) `rank R(G,p;E∖E',V∖V') =
> rank R(G/E',p₂)` via the deleted-`v*`-columns identity + **Lemma 5.1** pin-a-body; (6.3)+(6.5) ⟹ `rank R(G,p)
> ≥ rank R(G',p₁) + rank R(G/E',p₂) = D + D(|V|−2) − k = D(|V|−1) − k`; **Lemma 6.3** statement = the simple +
> `G/E'`-simple arm, "nonparallel" realization, same rank, via the (6.6) intersection-hinge map — confirms 6.3
> is the L5b simple arm and **6.5 is the rest**, deferred to L8). No `.lean`/`.tex` edits this pass.

**Citation.** Katoh–Tanigawa 2011, *Discrete Comput. Geom.* **45**, 647–700; **Lemma 6.2**, §6.2, p. 673–674
(the non-simple sub-case of the proper-rigid-subgraph case of the all-`k` Theorem 5.5 induction). The
parallel-pair `G[{e,f}]` proper-rigidity uses `ẽ ∪ f̃` carrying `D` edge-disjoint spanning trees (KT's
multiplied-graph criterion, §3); the coincident-panel base realization `(G', p₁)` with `Π(a) = Π(b)` is
**Lemma 5.3**, p. 670; the deleted-`v*`-columns rank invariance `rank R(G/E',p₂;E∖E',V∖V') = rank R(G/E',p₂)`
is **Lemma 5.1** (the [29] = Tay–Whiteley pin-a-body fact), p. 668; the contraction `G/E'` minimal-`k`-dof
with `|V(G/E')| < |V|` is **Lemma 3.5**, p. 658. The IH (6.1) is KT's all-`k` inductive hypothesis, p. 671.
All verified against the PDF this pass.

**Red-node consistency gate (run on the L5 inputs).** L5 *mints* its non-simple producer node — there is **no
existing all-`k` Lemma-6.2 realization node** in the dep-graph (structural-edit mode). The two relevant existing
nodes were re-read end-to-end: `lem:case-I-dispatch` (case-i.tex, the `h65` red node) — statement and proof
route through the 6.3-vs-6.5 dispatch on `(G.rigidContract H r).Simple` and the Lemma-6.5 vertex-removal arm;
no `\uses` at a superseded node; **L5 does NOT touch it** (the 6.5 arm is L8, and L5's non-simple branch is
Lemma 6.2, a *different* KT sub-case — non-simplicity of `G` itself, not non-simplicity of the contraction).
`lem:case-I-realization` (the simple Lemma-6.3 arm, pinned to `case_I_realization`, green at the GP conclusion):
its statement carries `hSimple`/`hcSimple` and concludes `HasGenericFullRankRealization` — the L5b simple arm
consumes it verbatim (all-`k`-restated). `blueprint/lint.sh` expected green (no edits this pass; L5's nodes
mint at the build). All self-consistent; the L5 producer family plugs into the `hcontract` slot at L9.

**The slot the producer family fills.** L2's `hcontract` slot (§1.56(c) `minimal_kdof_reduction_all_k`), at
`P G = Pc G := (G.Simple → HasGenericFullRankRealization 2 n G) ∧ HasPanelRealization 2 n G` (§1.56(b) M4):

```text
hcontract : ∀ (k : ℤ) (G), G.IsMinimalKDof n k → 3 ≤ V(G).ncard →
  (∃ H, H.IsProperRigidSubgraph G n) →
  (∀ (k' : ℤ) (G'), G'.IsMinimalKDof n k' → V(G').Nonempty → V(G').ncard < V(G).ncard → Pc G') →
  Pc G
```

So the slot-filler receives `hG`, `3 ≤ ncard`, `⟨H, hH⟩`, and the guarded conditioned IH; it must conclude the
pair `Pc G = ⟨gp, bare⟩`. This is exactly the L4 `hcut`-slot shape with `¬ TwoEdgeConnected` replaced by
`∃ H, IsProperRigidSubgraph G n` — so L5 reuses L4's slot-filler architecture (the `.2` bare conjunct and the
`.1` GP conjunct as *separate* producers, mirroring how `theorem_55_generic` keeps `hcontract`/`hcontractGP`
as separate slots), differing only in the case math inside each conjunct.

**(a) The two-way dispatch — KT's trifurcation collapses to a `by_cases` on `G.Simple`.** KT p. 673 splits the
proper-rigid-subgraph case into **three** sub-cases: Lemma 6.2 (`G` not simple), Lemma 6.3 (`G` simple, `G/E'`
simple), Lemma 6.5 (the rest = `G` simple but *no* `(H, r)` has a simple contraction). The §1.56(d) `hcontract`
plan dispatches on `G.Simple` at the **top** level, folding 6.3 and 6.5 together as "the simple branch":

* **simple branch (`hSimple : G.Simple`)** → the §1.55(c) `hcontractGP`-dispatch precedent, generalized to
  all-`k`: forgetful M4 (`hasPanelRealization_of_generic`) ∘ the all-`k`-restated GP `case_I_realization`. The
  GP `case_I_realization` is itself the 6.3-vs-6.5 dispatch (the landed 22h `theorem_55_d3` wiring inlines a
  `by_cases` on `(G.rigidContract H r).Simple`: positive → `case_I_realization` directly = Lemma 6.3; negative →
  the carried `h65` = Lemma 6.5). **L5's simple branch leaves the 6.5 sub-arm carried as `h65` (= L8); it does
  NOT build Claim 6.6 / the Π°-placement.** What L5 builds in the simple branch is the *all-`k` restate* of
  `case_I_realization` (it is currently `0`-dof-only: `hG : G.IsMinimalKDof n 0`, `hIH` over `IsMinimalKDof n 0`)
  plus the M4-forgetful wrap to the bare conjunct.
* **non-simple branch (`¬ G.Simple`)** → **KT Lemma 6.2 (NEW math)**: the coincident-panel splice. This is the
  L5a deliverable, the genuinely new content of L5. It concludes the **bare `HasPanelRealization` conjunct only**
  (KT 6.2 produces no nonparallel realization — coincident panels mean GP fails); its GP conjunct is
  *vacuously discharged* because the `.1` conjunct `G.Simple → HasGenericFullRankRealization` has an
  unsatisfiable antecedent on this branch (`¬ G.Simple`, so `fun hSimple => absurd hSimple hnsimple`).

So the slot-filler is, schematically:
```text
hcontract := fun k G hG hV3 hex hIH =>
  by_cases hSimple : G.Simple
  · ⟨fun _ => case_I_realization_all_k_gp … hSimple … (hIH·full),     -- L5b: 6.3 arm + h65 carry
     hasPanelRealization_of_generic … (case_I_realization_all_k_gp … hSimple …)⟩  -- M4 forgetful
  · ⟨fun hS => absurd hS hSimple,                                      -- GP vacuous on ¬Simple
     case_I_realization_nonsimple … hG hex (fun … => (hIH …).2)⟩       -- L5a: KT Lemma 6.2, bare
```
(Exact wiring at L5b; the GP-vacuity on the non-simple branch is the same `not_simple`-absurd idiom as
`hbaseGP`'s parallel-pair vacuity, §1.54(a1).)

**(b) V6 RESOLVED — N6a cannot be re-aimed; the non-simple branch is a fresh `BodyHingeFramework`-native
producer.** The carries table (§1.56(d)) flagged V6 as "read N6a's exact statement at the L5 pin and re-aim at
the honest carrier (its `hends`/`hsupp` shape was built for the weak motive)." Reading the landed N6a family
(GenericityDevice.lean:891–1107) settles V6 **against** a re-aim, for three independent reasons:

1. **N6a concludes the deleted motive.** `hasFullRankRealization_of_splice_of_supportExtensor` (:915) and its
   leg-native sibling (:1095) both conclude `PanelHingeFramework.HasFullRankRealization k G` — the M5-deleted
   weak motive (Decision 1, §1.55(a): "no weak form survives to be cited"). They cannot be re-pointed at M2
   `HasPanelRealization` by a signature edit: `HasFullRankRealization` is `∃ Q, Q.graph = G ∧
   Q.toBodyHinge.IsInfinitesimallyRigidOn V(G)` (rigidity-on-`V(G)`), whereas M2 demands a *deficiency-aware
   rank equality* + genuine hinges + containment + nonzero panels — a strictly richer conclusion that the
   N6a proof (which routes through the genericity *device* `hasFullRankRealization_of_independent_panelRow`)
   does not establish.
2. **N6a is `PanelHingeFramework`/`ofNormals`-bound; M2 is `BodyHingeFramework`-native.** N6a's legs and seed
   live on `ofNormals G ends q₀` (derived hinges = the meet of two selected normals) — exactly the carrier the
   §1.56(a) expressiveness finding rules out for the coincident-panel case (`panelSupportExtensor n n = 0`, so
   a derived-hinge framework cannot carry a genuine hinge in a *coincident* panel). M2 is on the free-hinge
   `BodyHingeFramework` precisely so the cut/splice hinge can be a genuine `(d−2)`-flat chosen *inside* the
   common panel even when the two panels coincide.
3. **The honest non-simple producer already has its precedent — L4a.** The landed `case_cut_edge_realization`
   (CaseI.lean:7588) is the `BodyHingeFramework`-native bare producer for the *other* reduction case (the cut),
   assembled from IH `HasPanelRealization` side frameworks + a coincident-panel-tolerant cut hinge
   (`exists_extensor_in_two_panels`) + the block-rank brick `le_finrank_span_rigidityRows_of_cut` + B2. **KT
   Lemma 6.2 is structurally the same assembly** — two legs (`G' = G[{e,f}]` and `G/E'`) glued over a single
   shared/cut structure, block-triangular rank addition, B2 closing. So V6's resolution is: **N6a is dead
   infrastructure for the honest motive; L5a builds the Lemma-6.2 producer fresh in the L4a idiom, on the
   `BodyHingeFramework` carrier, reusing `exists_extensor_in_two_panels` for the coincident-panel hinge.**

   *The block-rank brick fit (the one item to confirm at the L5a build).* L4a's `le_finrank_span_rigidityRows_of_cut`
   adds two *vertex-disjoint* side blocks over a cut with `≤ 1` crossing edge. KT 6.2's two legs are `G' =
   G[{e,f}]` on `V' = {a, b}` and `G/E'` on `(V∖V')∪{v*}`, which **share** the contracted body `v*`/`{a,b}` — they
   are *not* vertex-disjoint (they overlap in the splice body). So the lower-bound engine for L5a is **not** the
   L4a disjoint-block brick verbatim; it is the **shared-body splice** pattern KT eq. (6.3)–(6.5) describes (the
   `G'` block is rigid on `V' = {a,b}` and the `G/E'` block reads `R(G/E',p₂)` after deleting the `v*`-columns).
   The landed splice-glue infrastructure for *this* shape is `isInfinitesimallyRigidOn_of_splice` (used by N6a at
   :929–931) — but that glue establishes *rigidity*, which is only the `def = 0` instance. For general
   `k`-dof legs (the non-simple branch has `def(G̃) = k`, possibly `> 0`), the splice produces a *rank lower
   bound*, not rigidity, so L5a needs the **rank-additive form of the splice over a shared body** — the L5a
   block-rank brick. **This is the one genuinely-new linear-algebra piece of L5** (the §1.56(d) "eq. (6.3)–(6.5)
   rank addition"), the shared-body sibling of L4a's disjoint-body `le_finrank_span_rigidityRows_of_cut`. See
   (c)'s `le_finrank_span_rigidityRows_of_splice` pin.

**(c) The L5a non-simple producer + its block-rank brick (the NEW Lean).** Two declarations, the brick first.

*The shared-body splice block-rank brick* (`lem:rigidityRows-splice-rank-add`; KT Lemma 6.2 eq. (6.3)–(6.5)
block-triangular core; the shared-body sibling of L4a's disjoint-body brick). For a body-hinge framework `F`
whose links partition over a proper rigid subgraph `H ≤ F.graph` (the `E(H)` rows) and its edge-complement
`F.graph ＼ E(H)` (the remaining rows), sharing the contracted body, the rigidity-row span's dimension is at
least the `H`-block (rigid, `D(|V(H)|−1)`) plus the contraction block (`= rank R(G/E')` by the deleted-columns
Lemma 5.1 identity):
```lean
/-- **Shared-body splice block-rank addition** (`lem:rigidityRows-splice-rank-add`; KT Lemma 6.2
eq. (6.3)–(6.5); Phase 22i L5a). For a body-hinge framework `F` on `G`, a proper rigid subgraph
`H ≤ G` with representative `r ∈ V(H)`, the rigidity-row span dimension is at least the `H`-leg span
plus the contraction-leg span (the rows carried by `E(G) ∖ E(H)`, read on the surviving body set
`(V(G) ∖ V(H)) ∪ {r}`). -/
theorem BodyHingeFramework.le_finrank_span_rigidityRows_of_splice [Finite α] [Finite β]
    (F : BodyHingeFramework k α β) {H : Graph α β} {r : α}
    (hH : H ≤ F.graph) (hr : r ∈ V(H))
    (hC : ∀ e u v, F.graph.IsLink e u v → F.supportExtensor e ≠ 0)
    (… leg/shared-body classification hypotheses …) :
    Module.finrank ℝ (Submodule.span ℝ (F.restrictTo V(H)).rigidityRows)
      + Module.finrank ℝ (Submodule.span ℝ (F.restrictTo ((V(F.graph) \ V(H)) ∪ {r})).rigidityRows)
      ≤ Module.finrank ℝ (Submodule.span ℝ F.rigidityRows)
```
Design notes: **(i)** the structural reason is KT (6.3)'s block-triangular shape — the `E(H)` rows read only
the `V(H)` bodies (top-left block `R(G', p₁)`, the `0` off-block), and the `E∖E(H)` rows are `R(G,p;E∖E',V∖V')`
which by (6.4)/(6.5) has the same rank as `R(G/E',p₂)` (the deleted-`v*`-columns Lemma-5.1 identity, the
already-landed pin-a-body machinery `finrank_span_rigidityRows_of_rigidOn`/the pinned-block suite). The legs
**share** the body `r`/`v*`, so unlike L4a this is *not* a disjoint-block direct sum; the additivity comes from
the block-triangular `0` in the top-right, the same `Submodule.finrank_sup` argument restricted to the
upper-triangular structure (the surviving-body span of the contraction leg meets the `V(H)`-block span only in
the shared `r`-coordinates, which the IH rank accounting already nets out). **(ii)** `restrictTo` is the landed
side-framework constructor (used by L4a). **(iii)** `buildable`, not research-shaped — it is KT's elementary
block-triangular argument, and the device-direct precedent `isInfinitesimallyRigidOn_of_splice` (the `def=0`
instance) already establishes the splice glue; L5a generalizes it from *rigidity* to a *rank lower bound* the
same way L4a generalized the cut split from B1 to the `≥`-then-B2 pattern. **Flag V6-a:** confirm at the L5a
build whether the shared-body block-triangular additivity reuses `isInfinitesimallyRigidOn_of_splice`'s span
decomposition directly (likely — it is the same glue, read as a span-`⊔` rather than a rigidity conclusion) or
needs the explicit `Submodule.finrank_sup`/block-triangular `0`-block argument.

*The L5a non-simple bare producer* (`lem:case-I-realization-nonsimple`; KT Lemma 6.2; the L4a `case_cut_edge_realization`
analogue for the proper-rigid-subgraph case). It receives the `hcontract` slot's `⟨H, hH⟩` and the `.2`-projected
conditioned IH:
```lean
theorem case_I_realization_nonsimple [DecidableEq β] [Finite α] [Finite β] {n : ℕ}
    (hD : 2 ≤ Graph.bodyBarDim n) (hn : Graph.bodyBarDim n = screwDim 2)
    {k : ℤ} (G : Graph α β) (hG : G.IsMinimalKDof n k) (_hV3 : 3 ≤ V(G).ncard)
    {H : Graph α β} (hH : H.IsProperRigidSubgraph G n)
    (hIH : ∀ (k' : ℤ) (G' : Graph α β), G'.IsMinimalKDof n k' → V(G').Nonempty →
      V(G').ncard < V(G).ncard → HasPanelRealization 2 n G') :
    HasPanelRealization 2 n G
```
Body: from `hH` choose the representative `r ∈ V(H)` (`hH.vertexSet_nonempty`); `couple_geometry_of_isProperRigidSubgraph
hH hr` gives the two legs `H ≤ G` and `G ＼ E(H) ≤ G` sharing `r`, with the cover. The contraction `G.rigidContract
H r` is `IsMinimalKDof n k` and strictly smaller by **`rigidContract_isMinimalKDof`** (V4 — *already all-`k` in
the landed Lean*, no generalization) + `rigidContract_vertexSet_ncard` (`|V(G/E')| = |V(G)| − |V(H)| + 1 < |V|`
since `|V(H)| ≥ 2`); the `H`-leg is minimal-`0`-dof and smaller (`IsProperRigidSubgraph` ⟹ `H.IsMinimalKDof n 0`,
`|V(H)| < |V|`). So the IH applies to both legs, giving `HasPanelRealization` side frameworks `F_H`, `F_c`.
Assemble `F : BodyHingeFramework` and `normal` by edge dispatch (`E(H)` rows from `F_H`, `E∖E(H)` rows from `F_c`,
exactly KT (6.2)), with the splice/shared body `r`'s panel **coincident** (`normal r` shared, `Π(a) = Π(b) =
Π(v*)`); the splice hinge in the common panel is `exists_extensor_in_two_panels (normal a) (normal b)` **at
coincident normals** (`a, b` the parallel-pair endpoints both carry the contraction's panel — this is exactly
the `n₁ = n₂` use the L4a brick already supports). Rank: `≥` from `le_finrank_span_rigidityRows_of_splice` (the
(b) brick) + the two IH rank conjuncts + the deficiency arithmetic `k = k` (the `H`-leg contributes `D(|V(H)|−1)`
since `def(H̃) = 0`, the contraction leg `D(|V(G/E')|−1) − k = D(|V|−|V(H)|) − k`, summing to `D(|V|−1) − k` by
`|V(G/E')| = |V|−|V(H)|+1`); `≤` from B2 (`finrank_span_rigidityRows_add_deficiency_le`); antisymmetry closes the
M2 equality. *Buildable from the (b) brick + IH + B2,* transversality-free (the coincident-panel hinge is the
whole point — no GP needed; this is why the non-simple branch concludes only the bare conjunct).

**(d) The L5b simple-branch all-`k` GP restate + the dispatch.** L5b restates `case_I_realization` (CaseI.lean:2155)
from `0`-dof-only to all-`k`, then assembles the full `hcontract` slot-filler. Two pieces:

*The all-`k` GP restate of `case_I_realization`.* The landed `case_I_realization` is `0`-dof-bound (`hG :
G.IsMinimalKDof n 0`, `hIH` over `IsMinimalKDof n 0`, concludes `HasGenericFullRankRealization k n G` at `def =
0`). The all-`k` form takes `{k : ℤ}`, `hG : G.IsMinimalKDof n k`, the all-`k` conditioned IH, and concludes the
GP motive at the graph's own deficiency:
```lean
theorem case_I_realization_all_k [DecidableEq β] [Finite α] [Finite β] {n : ℕ}
    (hD : 3 ≤ Graph.bodyBarDim n) (hn : Graph.bodyBarDim n = screwDim 2)
    {k : ℤ} (G : Graph α β) (hG : G.IsMinimalKDof n k) (_hV3 : 3 ≤ V(G).ncard)
    {H : Graph α β} (hH : H.IsProperRigidSubgraph G n) {r : α} (hr : r ∈ V(H))
    (hSimple : G.Simple) (hcSimple : (G.rigidContract H r).Simple)
    (hIH : ∀ (k' : ℤ) (G' : Graph α β), G'.IsMinimalKDof n k' → V(G').Nonempty →
      V(G').ncard < V(G).ncard →
      (G'.Simple → PanelHingeFramework.HasGenericFullRankRealization 2 n G') ∧
        HasPanelRealization 2 n G') :
    PanelHingeFramework.HasGenericFullRankRealization 2 n G
```
This still carries `hcSimple` (the Lemma-6.3 case hypothesis) — it is the **6.3 arm**. The restate from `0`-dof
to all-`k` is **V-restate-shaped, not research-shaped**: the landed proof's rank arithmetic threads `def = 0`
through `couple_geometry`/`rigidContract_exterior_rank_transport_htransport`/the device; the all-`k` form replaces
each `def = 0` use with the graph's `def(G̃) = k` (the M2/M3 ℤ-cast rank conjuncts already carry the deficiency
term), exactly the `0`-dof → all-`k` thread the L4 producers (`case_cut_edge_realization{,_gp}`) already
demonstrate. **Flag V6-b:** confirm at the L5b build that the landed `case_I_realization`'s rank-transport leg
(`rigidContract_exterior_rank_transport_htransport`, CaseI.lean:1642 — currently `hdef : (G.rigidContract H
r).deficiency n = 0`) generalizes to the contraction's actual `def = k`; expected mechanical (the transport is
a rank *identity*, deficiency-agnostic in its core), but it is the one all-`k` thread L5b must verify.

*The dispatch* (the `hcontract` slot-filler), wiring (a)'s schematic: `by_cases hSimple : G.Simple`; positive
arm `⟨fun _ => case_I_realization_all_k … hSimple hcSimple (hIH·full), hasPanelRealization_of_generic …
(case_I_realization_all_k …)⟩` where `hcSimple` comes from the inner `by_cases` on `(G.rigidContract H r).Simple`
(positive → Lemma 6.3 = `case_I_realization_all_k`; negative → the carried `h65`, L8); negative arm `⟨fun hS =>
absurd hS hSimple, case_I_realization_nonsimple … (fun … => (hIH …).2)⟩`. The `h65` carry on the simple branch's
non-simple-contraction sub-case is **unchanged from 22h** (it stays a named hypothesis until L8); L5 does not
discharge it. The M4 forgetful wrap needs `[G.Loopless]` (from `hSimple.toLoopless`) and `2 ≤ V(G).ncard` (from
`_hV3`).

**(e) Blueprint disposition.** Mirrors §1.62(e)'s green-bare + GP-sibling split, for the proper-rigid-subgraph
case. L5a mints **one new node** `lem:case-I-realization-nonsimple` (case-i.tex, beside `lem:case-I-realization`)
for the non-simple branch's bare `HasPanelRealization`, `\uses`-ing `def:genuine-hinge-realization` (M2),
`lem:cut-edge-decomposition`'s sibling for the splice decomposition (or the proper-rigid-subgraph bricks directly),
`def:rank-hypothesis`, `prop:rigidity-matrix-prop11` (B2's hub), and a small new node
`lem:rigidityRows-splice-rank-add` for the (c) shared-body brick (rigidity-matrix.tex, beside L4a's
`lem:rigidityRows-cut-rank-add`) if it earns one (else fold into the producer's `\uses`). L5b restates
`lem:case-I-realization` in place to the all-`k` form (`\lean{…case_I_realization_all_k}` — a statement change,
so **grep `blueprint/src` for `case_I_realization` per the structural-edit gate** before committing L5b;
`lem:case-I-dispatch` (the `h65` node) keeps its `\lean{}` and stays red, unchanged). The L9 spine consumes the
conjunction `⟨gp, bare⟩` at the `hcontract` slot. No statement-grep ripple from L5a (additive node; the legacy
`theorem_55_d3` spine reaches Case I only at `0`-dof via `case_I_realization`, which L5b restates, not L5a).

**(f) The L5 slice cut (exact-signature build leaves, build order).** Two layers, the non-simple bare producer
first (it is the new math and carries no `h65`/restate entanglement):

* **L5a** — `BodyHingeFramework.le_finrank_span_rigidityRows_of_splice` (the shared-body block-rank brick, (c))
  + `case_I_realization_nonsimple` (the non-simple bare producer, (c)) in CaseI.lean (beside
  `case_cut_edge_realization`) + RigidityMatrix.lean (the brick, beside L4a's `le_finrank_span_rigidityRows_of_cut`).
  The brick is the only genuinely-new math; the producer is IH-plumbing + the brick + B2 + the landed
  `exists_extensor_in_two_panels`. Mints `lem:case-I-realization-nonsimple` (+ optionally
  `lem:rigidityRows-splice-rank-add`). **First concrete L5 commit.** *Buildable* (V6-a, the brick's reuse of
  `isInfinitesimallyRigidOn_of_splice`'s decomposition, resolves at this build).
* **L5b** — `case_I_realization_all_k` (the all-`k` GP restate of `case_I_realization`, (d)) + the `hcontract`
  slot-filler dispatch (the (a) `by_cases`, wiring the simple arm via M4 ∘ `case_I_realization_all_k` and the
  non-simple arm via L5a, with the `h65` carry threaded unchanged). In CaseI.lean. Statement change to
  `case_I_realization` → **grep `blueprint/src` per the structural-edit gate**; restates `lem:case-I-realization`
  to the all-`k` form. Completes the full `Pc` slot-filler `⟨gp, bare⟩` for the `hcontract` slot. *Buildable on
  L5a* (V6-b, the rank-transport leg's all-`k` thread, resolves at this build).

If the full pin won't fit one sitting at build time: L5a alone is a clean stopping point (the new math + the
non-simple node green); L5b (the restate + dispatch) is then a separate sitting. The `h65` carry is **L8** and
is out of L5's scope on both leaves.

*Verification items L5 resolves:* **V6** (N6a's statement vs the honest carrier) — **RESOLVED**: N6a is dead
infrastructure for the M2 motive (it concludes the deleted `HasFullRankRealization` and is `ofNormals`-bound),
so L5a builds the Lemma-6.2 producer fresh on the `BodyHingeFramework` carrier in the L4a idiom, reusing
`exists_extensor_in_two_panels` for the coincident-panel hinge; V4 (`rigidContract_isMinimalKDof` all-`k`)
confirmed **already discharged** in the landed Lean. *Verification items L5 adds:* **V6-a** (the shared-body
block-rank brick's reuse of the landed splice-glue span decomposition; bounded, resolve at L5a's build);
**V6-b** (the all-`k` thread through `case_I_realization`'s rank-transport leg; expected mechanical, resolve at
L5b's build). Both `buildable`; neither is a research-shaped open question (the only NEW math in L5 is the
(c) shared-body block-rank brick, and it is KT's elementary (6.3)–(6.5) block-triangular argument).

---

### 1.64 The L5a RE-PIN — correcting §1.63(c)/(f): the contraction leg is `rigidContract` (a COLLAPSE), not `induce`; the (6.3)–(6.5) additivity is a NEW general-rank block-triangular brick assembled from landed rigidity-FREE pieces (`extProj` row-vanishing ⊕ the collapse row-correspondence ⊕ the deficiency-aware `_of_le_finrank` extractor ⊕ the general-rank Lemma 5.1 column-deletion `finrank_pinnedMotions_add_screwDim`); it is **buildable, NO IH/motive change** — but the projected-image-rank step is genuinely new linear algebra (not a one-line brick, not the rigidity-gated `injOn_extProj` route), flagged for the L5a build (2026-06-13)

> **Docs-only design pass (the L5a re-pin).** Lean read this pass — declarations + line numbers, all
> **verified this pass against the landed Lean** (the boundary-pair postmortem cost a revert, so every
> load-bearing signature below was re-read, not trusted from the prior pin's prose):
> CaseI.lean — `extProj` (:821, the column projection) + `extProj_apply_mem`/`_not_mem` (:827/:832) +
> `extProj_apply_collapseTo` (:847) + `hingeRow_comp_extProj_eq_zero` (:862, **rigid-block rows vanish under
> the projection — NO rigidity hypothesis**) + `hingeRow_collapseTo_comp_extProj_eq` (:884) +
> `panelRow_collapseTo_comp_extProj_dualMap` (:940, **the collapse row-correspondence — NO rigidity
> hypothesis**) + `extProj_range_eq_iInf_ker_proj` (:971) +
> `injOn_extProj_dualMap_rigidityRows` (:1091, **GATED on `F.IsInfinitesimallyRigidOn F.graph.vertexSet` —
> full rigidity — this is the Claim-6.4 "projection loses zero rank"; UNUSABLE at `def = k > 0`**) +
> `exists_independent_panelRow_subfamily_of_rigidOn_linking_set_proj` (:1130, same full-rigidity gate);
> `rigidContract_exterior_rank_transport` (:1553, **`hdef : (G.rigidContract H r).deficiency n = 0`** — the
> whole U3a/U3b/U2 transport is 0-deficiency) + `..._htransport` (:1642, same); `case_I_realization` (:2155,
> the landed `0`-dof simple Lemma-6.3 arm) + `hasGenericFullRankRealization_of_couple_asymm_ofNormals_set`
> (:745, the splice coupler — its docstring :715–765 states explicitly that the contraction-leg
> complement-isolation equality `finrank (pinnedMotionsOn sc) = D·|scᶜ|` is **FALSE** for the deficient
> contraction leg; the project's `finrank_pinnedMotionsOn_le` proves only the *upper* bound) +
> `isInfinitesimallyRigidOn_vertexSet_of_span_le_rigidityRows` (:1772, the rank-nullity core) +
> `case_cut_edge_realization` (:7588, the landed L4a bare producer, the `induce`-leg precedent — note its two
> legs are genuine `induce` subgraphs, the structural reason it works bare and the splice can't);
> RigidityMatrix.lean — `finrank_pinnedMotions_add_screwDim` (:2694, **Lemma 5.1, the deleted-`v∗`-columns
> rank identity at GENERAL rank — `finrank (pinnedMotions v) + D = finrank Z`, NO rigidity, holds at any
> deficiency**) + `le_finrank_span_rigidityRows_of_cut` (:2991, L4a's disjoint-block brick — `S₁ ⊓ S₂ = ⊥` by
> the V₁/V₂ projection, NOT the splice's shared-body shape) + `rigidityRows` (:920) + `hingeRowBlock` (:754);
> GenericityDevice.lean — `exists_independent_panelRow_subfamily_of_le_finrank` (:718, **W6e, the
> deficiency-aware / rigidity-FREE extractor: a rank lower bound `N ≤ finrank (span rigidityRows)` yields `N`
> independent linking panel rows** — the deficient-leg tool L4b-1 already uses) +
> `finrank_span_rigidityRows_add_deficiency_le` (:562, B2, the free `V(G)`-relative `≤`); Pinning.lean —
> `pinnedMotionsOn` (:917) + `pinnedMotionsOn_singleton` (:937) + `finrank_iInf_ker_proj_eq` (:1076);
> ReducibleVertex.lean — `rigidContract = (G ＼ E(H)).map (collapseTo r V(H))` (:1052) +
> `vertexSet_rigidContract = collapseTo r V(H) '' V(G)` (:1056) + `rigidContract_vertexSet_ncard`
> (`= (|V(G)|−|V(H)|)+1`, :1097); CaseI.lean — `Graph.rigidContract_vertexSet_inter_eq_singleton`
> (:1597, `V(G.rigidContract H r) ∩ V(H) = {r}` — **the single shared/deleted column is `r = v∗`**);
> Contraction.lean — `rigidContract_isMinimalKDof` (:696, **all-`k` already**, V4 discharged);
> PanelLayer.lean — `exists_extensor_in_two_panels` (:631, the coincident-panel hinge, works AT `n₁ = n₂`);
> Deficiency.lean — `isKDof_zero_of_parallel_pair` (:606), `IsProperRigidSubgraph` (:428),
> `couple_geometry_of_isProperRigidSubgraph` (CaseI.lean:560). **KT re-read against the PDF this pass**
> (offset `printed p.N = pdf page (N − 646)`): **p. 673–674 §6.2 eqs. (6.2)–(6.5) verbatim** (the block-
> triangular matrix (6.3), the (6.4) `p|E∖E' = p₂` entry equality, the (6.5) deleted-`v∗`-columns + Lemma 5.1
> rank identity, the (6.3)+(6.5) `≥` rank chain). No `.lean`/`.tex` edits this pass.

**Citation.** Katoh–Tanigawa 2011, *Discrete Comput. Geom.* **45**, 647–700; **Lemma 6.2**, §6.2, p. 673–674.
The deleted-`v∗`-columns rank invariance `rank R(G/E', p₂; E∖E', V∖V') = rank R(G/E', p₂)` is **Lemma 5.1**
(the [29] = White–Whiteley pin-a-body fact), p. 668 — landed at general rank as
`finrank_pinnedMotions_add_screwDim`. The block-triangular `≥` is KT eq. (6.3), elementary linear algebra
(a lower-triangular block matrix `[[A,0],[∗,B]]` has `rank ≥ rank A + rank B`). All verified vs the PDF.

**(a) What §1.63 got wrong, restated precisely (the verified diagnosis).** §1.63(c) stated the splice's second
leg as `induce ((V(G)∖V(H))∪{r})` and the brick as a *bare, transversality-free* `S_H + S_c ≤ S` span split
mirroring L4a. Two independent errors, both confirmed against the landed Lean this pass:

1. **The contraction leg is a COLLAPSE, not an induced subgraph.** `rigidContract G H r =
   (G ＼ E(H)).map (collapseTo r V(H))` (ReducibleVertex.lean:1052) and `induce ((V(G)∖V(H))∪{r})` have the
   **same vertex set** (`vertexSet_rigidContract` ∩ `rigidContract_vertexSet_inter_eq_singleton`: both are
   `(V(G)∖V(H)) ∪ {r}`), but `induce` **drops** every crossing edge `δ_G(V(H))` (an edge with one endpoint
   inside `V(H)∖{r}`), whereas `rigidContract` **keeps** it, relabelled to `r`. So `rank R(induce-leg) =
   D(|V|−2) − def((induce-leg)~)`, a **strictly weaker** lower bound (the induce-leg drops constraints, raising
   its deficiency above `k`), which the producer cannot close against the `D(|V|−1)−k` target. And the IH does
   NOT realize the induce-leg — it realizes the **contraction** `G.rigidContract H r`, which is minimal-`k`-dof
   by `rigidContract_isMinimalKDof` (already all-`k`, V4). The brick must read the contraction's rows.
2. **The (6.3)–(6.5) additivity is NOT a bare span split.** §1.63 framed it as "the same `Submodule.finrank_sup`
   argument as L4a." But L4a's `le_finrank_span_rigidityRows_of_cut` works bare **only because its two legs are
   vertex-DISJOINT** (`S₁ ⊓ S₂ = ⊥` by the V₁/V₂ coordinate projection) with ≤1 crossing edge. The splice's two
   legs (`H`-block on `V(H)` and the surviving block on `(V∖V(H))∪{r}`) **share the contracted body `r`** and
   have **many** crossing edges (all of `δ_G(V(H))`, relabelled into the surviving block) — they are not disjoint
   and the L4a disjointness proof does not transfer. KT (6.3) is a genuine **lower-triangular** block matrix
   `[[R(G',p₁), 0],[∗, R(G,p;E∖E',V∖V')]]`, not a block-diagonal one.

**(b) THE KEY SUBTLETY RESOLVED — `def = k > 0` and Lemma 5.1 (the crux, and why the row-96/§1.63 pins went
wrong).** The landed `case_I_realization` route (and its `injOn_extProj_dualMap_rigidityRows` /
`rigidContract_exterior_rank_transport`) is **`0`-dof-bound at the deepest level, not merely in its hypotheses**:
its contraction leg `G.rigidContract H r` is itself minimal-**`0`**-dof (`hKmin`, CaseI.lean:2242), so its IH
realization is **fully rigid** (`HasGenericFullRankRealization`), and the Claim-6.4 machinery
`injOn_extProj_dualMap_rigidityRows` requires exactly that (`hrig : F.IsInfinitesimallyRigidOn
F.graph.vertexSet`, CaseI.lean:1093; `rigidContract_exterior_rank_transport` requires `hdef = 0`, :1555).

At `def(G̃) = k > 0` (the non-simple Lemma-6.2 case, and the general Case I), the contraction
`G.rigidContract H r` is minimal-**`k`**-dof, so its realization is **NOT** fully rigid — `def = k > 0` means
`rank R(G/E',p₂) = D(|V(G/E')|−1) − k < D(|V(G/E')|−1)`. **The rigidity-gated extProj/Claim-6.4 machinery does
not apply.** This is precisely why both the row-96 pin ("bare block-triangular, transversality-free") and the
§1.63 pin ("reuse the `case_I_realization` route" / "bare `induce` split") were wrong: there is no bare route,
AND the landed rigidity-gated route is unavailable at `k > 0`.

KT's actual `k > 0` argument (p. 674) uses **Lemma 5.1**, not Claim 6.4. The two are different facts:

* **Claim 6.4** (= `injOn_extProj_dualMap_rigidityRows`): "the exterior-column projection loses *zero* rank" —
  the projection `(extProj V(H)).dualMap` is *injective* on the full rigidity-row span. **Requires full
  rigidity** (`Z ⊔ W = ⊤`). Gives the surviving block its *full* rank `D(|sc|−1)`. Used at `def = 0` only.
* **Lemma 5.1** (= `finrank_pinnedMotions_add_screwDim`, RigidityMatrix.lean:2694): "deleting one body's `D`
  columns drops exactly the `D` trivial-motion dimensions, preserving rank" — `finrank (pinnedMotions v) + D =
  finrank Z`, equivalently `rank R(G; cols∖{v}) = rank R(G)`. **Holds at ANY rank, NO rigidity hypothesis.**
  This is the fact KT (6.5) invokes to equate the surviving block `R(G,p; E∖E', V∖V')` (= `R(G/E',p₂)` with the
  `v∗` columns deleted) with `rank R(G/E',p₂)`.

So the corrected `≥` chain (the buildable assembly): in the row-span view set `D := (extProj V(H)).dualMap`,
`S_H := span(H-block rows)`, `S_surv := span(surviving E∖E' rows of F)`:
- (i) `D` **kills `S_H`** — `hingeRow_comp_extProj_eq_zero` (rigidity-FREE), KT's top-right `0` of (6.3);
- (ii) the surviving rows, projected, **correspond row-for-row** to the projected collapsed rows over
  `G.rigidContract H r` — `panelRow_collapseTo_comp_extProj_dualMap` (rigidity-FREE), KT (6.4); so
  `D '' S_surv = D '' span(rigidContract-rows)`;
- (iii) `D` restricted to `span(rigidContract-rows)` **deletes exactly the single column `r = v∗`**
  (`rigidContract_vertexSet_inter_eq_singleton`: `V(G/E') ∩ V(H) = {r}`, so `extProj V(H)` zeroes only the `r`
  coordinate on the contraction's own bodies), and by **Lemma 5.1** that column-deletion *preserves rank*, so
  `finrank (D '' span(rigidContract-rows)) = rank R(G/E',p₂) = D(|sc|−1) − k`;
- (iv) **block-triangular `≥`:** `finrank (span F.rigidityRows) ≥ finrank (S_H ⊔ S_surv) ≥ finrank S_H +
  finrank (D '' S_surv)` — the second `≥` is rank-nullity for `D` on `S_H ⊔ S_surv` with `S_H ⊆ ker D` (i),
  `D '' (S_H ⊔ S_surv) = D '' S_surv` (i). With `finrank S_H = D(|sH|−1) = D` (the rigid parallel-pair block)
  and (iii), this is `≥ D + (D(|V|−2)−k) = D(|V|−1)−k`. Then B2 (`finrank_span_rigidityRows_add_deficiency_le`,
  landed, the free `≤`) closes the M2 rank equality by antisymmetry, exactly as L4a's producer does.

**This route requires NO motive change, NO IH statement-level change, and NO new `MvPolynomial`/genericity
content** (the splice is transversality-free / bare, the coincident-panel hinge is the whole point — GP fails,
so the non-simple branch concludes only the bare `HasPanelRealization`, exactly as §1.63(a) had it). The
bare `HasPanelRealization` conjunct **can** be produced without generic content (confirmed: the M2 motive is a
deficiency-aware rank equality at *some* framework, supplied by the fixed splice framework `F` itself, as in
the landed L4a producer).

**(c) HONESTY FLAG — the one genuinely-new linear-algebra brick (NOT a one-line brick; for coordinator
awareness, not a blocker).** Step (b)(iii) — `finrank ((extProj V(H)).dualMap '' span(rigidContract-rows)) =
rank R(G/E',p₂)` at general (deficient) rank — has **no landed precedent**. The landed
`injOn_extProj_dualMap_rigidityRows` is the *rigidity-gated* analogue (full injectivity on the full span); the
deficient version is a *rank identity via Lemma 5.1*, not injectivity. The pieces are all landed and
rigidity-free (`extProj` infra, the collapse row-correspondence, `finrank_pinnedMotions_add_screwDim`,
`extProj_range_eq_iInf_ker_proj`/`finrank_iInf_ker_proj_eq`), and the math is KT's elementary block-triangular
argument — so this is **`buildable`, not `research-shaped`**. But it is a *real new brick* (the
"general-rank shared-body block-triangular rank addition over a collapse"), likely several commits, **not** the
§1.63 "fold into the producer's `\uses`" one-liner. The honest statement: *the L5a math is settled and routes
entirely through landed rigidity-free pieces, but the new brick is a substantive assembly, not a trivial
mirror of L4a.* No decision needs coordinator adjudication — the route is determined; this flag is so the L5a
build is scheduled with the brick as its own slice (L5a-i), not underestimated as a one-liner again.

**(d) The corrected L5a signature(s).** Two declarations, the brick first. The brick is stated on the
*surviving-rows / contraction* shape (not the `induce` shape).

*The general-rank shared-body block-triangular rank-addition brick* (`lem:rigidityRows-splice-rank-add`; KT
Lemma 6.2 eq. (6.3)–(6.5); the collapse-aware, deficiency-tolerant sibling of L4a's disjoint-body
`le_finrank_span_rigidityRows_of_cut`). For a body-hinge framework `F` on `G` whose surviving rows correspond
to a contraction `G.rigidContract H r` realized at rank `Rc`, the rigidity-row span dimension is at least the
rigid `H`-block plus `Rc`:
```lean
/-- **General-rank shared-body splice block-rank addition** (`lem:rigidityRows-splice-rank-add`; KT
Lemma 6.2 eqs. (6.3)–(6.5); Phase 22i L5a). For a body-hinge framework `F` on `G`, a proper rigid
subgraph `H ≤ G` with representative `r ∈ V(H)`, where the `E(H)`-rows are the rigid block and the
`E(G) ∖ E(H)`-rows correspond (under `extProj V(H)`) to the contraction `G.rigidContract H r`'s rows,
the rigidity-row span dimension is at least the `H`-block span plus the contraction's rank `Rc`.
Unlike L4a this is a *lower-triangular* (shared-body) split — the surviving block reads the
contraction's rows after deleting the single `v∗ = r` column, whose deletion preserves rank by
Lemma 5.1 (`finrank_pinnedMotions_add_screwDim`); the additivity is the rank-nullity of
`(extProj V(H)).dualMap` (which kills the rigid block, `hingeRow_comp_extProj_eq_zero`). -/
theorem BodyHingeFramework.le_finrank_span_rigidityRows_of_splice [Finite α] [Finite β]
    (F : BodyHingeFramework k α β) {H : Graph α β} {r : α}
    (hH : H ≤ F.graph) (hr : r ∈ V(H)) (hHsub : V(H) ⊆ V(F.graph))
    (hC : ∀ e u v, F.graph.IsLink e u v → F.supportExtensor e ≠ 0)
    (… the surviving-rows ↔ contraction correspondence + the rigid-H-block hypotheses …) :
    -- the `H`-block term + the contraction's rank term ≤ the full span
    screwDim k * (V(H).ncard - 1)
      + (Module.finrank ℝ (Submodule.span ℝ «contraction-realization».rigidityRows))
      ≤ Module.finrank ℝ (Submodule.span ℝ F.rigidityRows)
```
The `(…)` is left as a design slot **deliberately** (this is a *pin*, not a build): the exact form of the
"surviving-rows ↔ contraction correspondence" hypothesis depends on whether the brick is stated against the
*contraction's realization framework* directly (cleanest — feed the IH framework `F_c` and the collapse
row-correspondence `panelRow_collapseTo_comp_extProj_dualMap` as a hypothesis) or reconstructs the
correspondence internally from `(G,H,r)` + `F`'s edge dispatch. The L5a build resolves which (V6-a, see (f));
both are buildable from the landed pieces enumerated in (b)/(c). The brick's **substance** is steps (b)(iii)+(iv)
— the rank-nullity of `(extProj V(H)).dualMap` + the Lemma-5.1 column-deletion — independent of that choice.

*The L5a non-simple bare producer* (`lem:case-I-realization-nonsimple`; KT Lemma 6.2; the contraction-leg
analogue of L4a's `case_cut_edge_realization`). It fills the `hcontract` bare slot (verified against
`theorem_55_generic`, PanelHinge.lean:1185, the `hcontract` slot the L9 spine wires):
```lean
theorem case_I_realization_nonsimple [DecidableEq β] [Finite α] [Finite β] {n : ℕ}
    (hD : 2 ≤ Graph.bodyBarDim n) (hn : Graph.bodyBarDim n = screwDim 2)
    {k : ℤ} (G : Graph α β) (hG : G.IsMinimalKDof n k) (_hV3 : 3 ≤ V(G).ncard)
    (hnsimple : ¬ G.Simple)
    (hIH : ∀ (k' : ℤ) (G' : Graph α β), G'.IsMinimalKDof n k' → V(G').Nonempty →
      V(G').ncard < V(G).ncard → HasPanelRealization 2 n G') :
    HasPanelRealization 2 n G
```
Body (KT Lemma 6.2 verbatim, the corrected leg structure): `¬ G.Simple` + `G.IsMinimalKDof` (loopless,
`loopless_of_isMinimalKDof`) gives multiple edges `e, f` joining some `a, b`; `G' := G[{e,f}]` is a proper
rigid subgraph (`isKDof_zero_of_parallel_pair`, the `ẽ ∪ f̃` carries `D` spanning trees on `{a,b}`); set
`r := a`. The contraction `G.rigidContract G' r` is minimal-`k`-dof and strictly smaller
(`rigidContract_isMinimalKDof` + `rigidContract_vertexSet_ncard_lt`); IH gives its `HasPanelRealization` `F_c`
at `rank = D(|V(G/E')|−1) − k = D(|V|−2) − k`. The `H = G'`-leg is minimal-`0`-dof on `{a,b}`, realized by
**Lemma 5.3** with **coincident panels** `Π(a) = Π(b)` (the coincident-panel hinge from
`exists_extensor_in_two_panels (normal a) (normal a)` AT `n₁ = n₂`, which the landed lemma supports) at rank
`D`. Assemble `F : BodyHingeFramework` by edge dispatch (`E' = {e,f}` rows from the `G'`-leg, `E∖E'` rows from
`F_c` pulled back through the collapse — KT's `p|E∖E' = p₂`, the `degeneratePlacement`-style normals), the
shared body `r = v∗`'s panel coincident with `Π(a) = Π(b)`. Rank `≥` from (d)'s brick + `F_c`'s rank conjunct
+ the arithmetic (`D + (D(|V|−2)−k) = D(|V|−1)−k`, `|V(G/E')| = |V|−2+1` since `|V(G')|=2`); rank `≤` from B2;
antisymmetry closes M2. *Transversality-free* — the coincident-panel hinge is the whole point, no GP. (Reuses
the `couple_geometry_of_isProperRigidSubgraph` cover + the L4a producer's `extF` edge-dispatch / `normal`
junk-value idioms.)

**(e) Blueprint disposition (unchanged from §1.63(e)).** L5a mints **one** new node
`lem:case-I-realization-nonsimple` (case-i.tex, beside `lem:case-I-realization`) for the non-simple branch's
bare `HasPanelRealization`, `\uses`-ing `def:genuine-hinge-realization` (M2), the proper-rigid-subgraph bricks,
`def:rank-hypothesis`, and `prop:rigidity-matrix-prop11` (B2's hub) — **plus** a new node
`lem:rigidityRows-splice-rank-add` for the (d) brick (rigidity-matrix.tex, beside L4a's
`lem:rigidityRows-cut-rank-add`). **Correction vs §1.63(e):** the brick earns its own node, NOT an optional
`\uses`-fold — it is the substantive new math (c), and it `\uses` `lem:rank-delete-vertex` (Lemma 5.1) and the
`extProj`/`lem:claim-6-4` row-vanishing + collapse-correspondence nodes. No statement-grep ripple from L5a
(additive node; the legacy `theorem_55_d3` spine reaches Case I only at `0`-dof via `case_I_realization`, which
**L5b** restates, not L5a). L5b is **unchanged from §1.63(d)** (the all-`k` GP restate of `case_I_realization`
+ the `by_cases G.Simple` dispatch; statement change → grep `blueprint/src` per the structural-edit gate).

**(f) The re-cut L5a slice (exact build leaves, build order).** Three leaves now (the brick is its own slice,
per the honesty flag (c)), the brick first:

* **L5a-i** — `BodyHingeFramework.le_finrank_span_rigidityRows_of_splice` (the (d) general-rank shared-body
  block-rank brick) in RigidityMatrix.lean (beside L4a's `le_finrank_span_rigidityRows_of_cut`). **This is the
  one genuinely-new math of L5** (the (b)(iii)+(iv) rank-nullity + Lemma-5.1 column-deletion assembly). Mints
  `lem:rigidityRows-splice-rank-add`. **First concrete L5 commit.** *Buildable* from the landed rigidity-free
  pieces (b)/(c); **V6-a** (the exact correspondence-hypothesis form: feed `F_c` + the collapse row-equality, vs
  reconstruct internally) resolves at this build. If the full brick won't fit one sitting, the rank-nullity
  half (`D` kills `S_H`, `D''(S_H⊔S_surv) = D''S_surv`) and the Lemma-5.1 column-deletion half
  (`finrank(D''span(rigidContract-rows)) = rank R(G/E')`) can split into two sub-commits.
* **L5a-ii** — `case_I_realization_nonsimple` (the (d) non-simple bare producer) in CaseI.lean (beside
  `case_cut_edge_realization`). IH-plumbing + the L5a-i brick + B2 + the coincident-panel Lemma-5.3 leg
  (`exists_extensor_in_two_panels` at `n₁ = n₂`) + the parallel-pair proper-rigidity
  (`isKDof_zero_of_parallel_pair`). Mints `lem:case-I-realization-nonsimple`.
* **L5b** — `case_I_realization_all_k` (the all-`k` GP restate of `case_I_realization`, §1.63(d), unchanged) +
  the `hcontract` slot-filler dispatch (the §1.63(a) `by_cases G.Simple`). Statement change to
  `case_I_realization` → grep `blueprint/src` per the structural-edit gate. Completes the full `Pc` slot-filler
  `⟨gp, bare⟩`. *Buildable on L5a-ii* (V6-b, the all-`k` thread through `case_I_realization`'s rank-transport
  leg, resolves here — and note (b) confirms the simple branch's contraction *is* `0`-dof only when... see
  the L5b caveat below).

> **L5b caveat for the build (verified this pass, recorded so the L5b agent does not re-discover it).** The
> simple-branch restate `case_I_realization_all_k` reuses the landed `case_I_realization`'s
> `rigidContract_exterior_rank_transport` leg, which is **`hdef = 0`-gated** (CaseI.lean:1555). At `def(G̃) =
> k > 0` the contraction `G.rigidContract H r` is minimal-`k`-dof, so that transport **does not apply** —
> meaning the *simple* all-`k` Case-I arm (Lemma 6.3 at `k > 0`) ALSO needs the (d) Lemma-5.1 block-triangular
> route for its surviving block, NOT a mechanical `0 → k` thread of the existing `injOn_extProj` leg. So
> **§1.63(d)/§1.63 (the V6-b "expected mechanical" flag) UNDER-scoped L5b**: the all-`k` simple Case-I restate
> is *not* a deficiency-substitution of the landed proof — it must re-route its surviving-block rank through
> the same (d) brick (the GP version: the surviving block reaches its rank `D(|sc|−1)−k` at the generic seed,
> via the deficiency-aware extractor `_of_le_finrank` rather than `_of_rigidOn_..._proj`). **This is still
> buildable** (the (d) brick + the L4b GP-conjunct machinery already in tree), but it is NOT mechanical, and
> L5b should be scoped as "re-route Case I's surviving block to the general-rank brick (GP variant)", not
> "substitute `k` for `0`". Flagged here, not silently carried.

*Verification items L5a adds/resolves:* **V6-a REOPENED → re-aimed** at the (d) general-rank brick's
correspondence-hypothesis form (resolve at L5a-i build); the §1.63 V6-a ("reuse
`isInfinitesimallyRigidOn_of_splice`'s span decomposition") is **superseded** — that decomposition is the
`def = 0` rigidity instance, unusable here, and the brick instead routes through Lemma 5.1. **V6-b re-scoped**
(see the L5b caveat: not mechanical; re-route through the (d) brick's GP variant). Neither is research-shaped.

### 1.65 The L5b design-pass — decomposing the all-`k` simple GP restate `case_I_realization_all_k`: the V6-b leaf is a genuinely-new `def = k > 0` *exterior-projected* rank-transport (a real brick, **P≈3**, NOT a clean assembly of landed pieces), because every landed projected-row tool is `0`-dof-gated; the leaf is pinned by signature but its internal route (route-1 projected rank-polynomial mirror vs route-2 pulled-back full-span + `hInj`) is left as a flagged open decision for the V6-b build, since both converge on needing a deficiency-aware analogue of the whole rigid U3a/U3b/U2-proj + rank-polynomial-proj chain (2026-06-13)

> ⚠️ **The §1.65(c) flagged route decision is RESOLVED by §1.66 (2026-06-13): route 1, NOT route 2 —
> route 2 (the splice brick + `hFc_surv_le`) is a DEAD END for the GP producer (mechanism mismatch). The
> L5b-i decomposition / V6-b `P≈3` rating / shared-core reuse in §1.65 all STAND; only the *internal route*
> (left open here) is now pinned, and L5b-ii is re-cut in §1.66(g). Read §1.66 for the corrected producer
> route; (a)–(g) below stand as the V6-b-leaf analysis §1.66 builds on.** The L5b-i *route-2 leaf*
> `exists_rankPolynomial_of_IH_relabel_linking` (built per (g) below) is superseded/dead under §1.66; its
> shared core `finrank_span_rigidityRows_ofNormals_relabel_eq` survives (route 1 reuses it).

> **Docs-only design pass (the L5b leaf decomposition + signature pin), all signatures re-verified against
> the LANDED Lean this pass** (the boundary-pair postmortem + the row-104 BLOCK both came from prose-trust;
> every load-bearing decl below was opened, not trusted from §1.64's or the BLOCK's prose):
> CaseI.lean — `case_I_realization` (:2284, the landed `0`-dof simple Lemma-6.3 arm) — its **`{n k : ℕ}`**,
> `hG : G.IsMinimalKDof n 0`, `hcSimple : (G.rigidContract H r).Simple`, IH conditioned at `n 0` →
> contraction is minimal-**`0`**-dof (`hKmin`, :2371) → IH `.1 hcSimple` gives `HasGenericFullRankRealization`
> (fully rigid) (:2379) → it feeds `rigidContract_exterior_rank_transport` (:2384) then
> `exists_rankPolynomial_of_rigidOn_linking_set_proj` (:2391) then
> `hasGenericFullRankRealization_of_couple_blockTriangular_ofNormals_set` (:2398); `rigidContract_exterior_rank_transport`
> (:1682, **`hdef : (G.rigidContract H r).deficiency n = 0`** at :1684 + `hQ : HasGenericFullRankRealization`
> at :1685) + `..._htransport` (:1771, `hdef = 0` at :1774, `hcSimple` at :1773, composes the rigid U3a
> `hasGenericRealization_transport_relabel` + U3b `exists_independent_panelRow_subfamily_of_rigidOn_linking_set_proj`
> + U2 `panelRow_collapseTo_comp_extProj_dualMap`); `exists_independent_panelRow_subfamily_of_rigidOn_linking_set_proj`
> (:1259, **`hrig : F.IsInfinitesimallyRigidOn F.graph.vertexSet`** at :1264 — full rigidity, the projected
> extractor); `hasGenericFullRankRealization_of_couple_blockTriangular_ofNormals_set` (:1988, **`hdef :
> G.deficiency n = 0`** at :2013 AND its `hsc_proj_indep` demands the projected surviving rows reach the FULL
> `screwDim k * (sc.ncard - 1)` = `D(|sc|−1)` at :2010 — both `0`-dof-gated, doubly unusable at `k > 0`);
> `case_I_realization_nonsimple` (:8479, the landed L5a-ii bare producer — the **template** for the splice-brick
> assembly: builds the fixed splice framework `F`, gets `Fc_fw` from the bare IH, discharges the four brick
> hyps; its `hFc_surv_le` (:8645) is the load-bearing precedent) + `hingeRow_collapseTo_comp_extProj_eq`
> (:884, **placement-free column-level row reconciliation under `(extProj t).dualMap`, NO rigidity, NO
> generic seed** — what makes `hFc_surv_le` dischargeable for ANY two frameworks sharing the annihilator
> block) + `hingeRow_comp_extProj_eq_zero` (:862, rigid-block rows vanish, also placement-free) +
> `panelRow_collapseTo_comp_extProj_dualMap` (:940, **the per-edge `panelRow` correspondence — stated AT the
> `degeneratePlacement r V(H) nrm` (:907), the collapsed-normal field, NOT at a free generic seed**) +
> `degeneratePlacement` (:907) + `extProj` (:821); the L5a-ii `hInj` kernel
> `finrank_span_rigidityRows_map_extProj_dualMap_of_inter_eq_singleton` (:1209, **rigidity-FREE, holds at ANY
> rank**, gives `finrank Sc = finrank (Sc.map Dmap)` from `V(Fc.graph) ∩ proj = {r}`) +
> `injOn_extProj_dualMap_rigidityRows_of_inter_eq_singleton` (:1176) + `rigidContract_vertexSet_inter_eq_singleton`
> (:1726); RigidityMatrix.lean — `le_finrank_span_rigidityRows_of_splice` (:3183, the L5a-i brick, general-rank,
> the four interface hyps `hFH_le`/`hFH_ker`/`hFc_surv_le`/`hInj`, abstract over `D`); GenericityDevice.lean —
> `exists_rankPolynomial_of_le_finrank_linking` (:1488, **the L4b-1 deficiency-aware rank polynomial: input
> `hN : N ≤ finrank (span (ofNormals G ends q₀).rigidityRows)` (:1494), NO rigidity; output a rational `Q ≠ 0`
> whose non-roots give `N ≤ finrank (span (ofNormals G ends q).rigidityRows)` at any `q`** — but its conclusion
> is the FULL rigidity-row span, NOT the `(extProj _).dualMap`-projected rows) + W6e
> `exists_independent_panelRow_subfamily_of_le_finrank` (:718, the deficiency-aware UNprojected extractor it
> builds on) + `exists_rankPolynomial_of_rigidOn_linking_set` (:1599, the rigid body-set rank polynomial the
> H-leg uses) + `exists_generalPosition_polynomial`; PanelHinge.lean — `HasGenericFullRankRealization` (:1035,
> the GP motive — `∃ Q, Q.graph = G ∧ Q.IsGeneralPosition ∧ rank = D(|V|−1) − def ∧ link-record ∧
> AlgIndep`) + `HasPanelRealization` (:1090, the bare motive) + `theorem_55_generic` (:1168, the `0`-dof spine,
> `hcontractGP` slot at :1190) + the `theorem_55_d3` (:7490) Case-I dispatch (:7552, `case_I_realization` on
> the 6.3-arm, `h65` on the 6.5-arm). **Confirmed: there is NO deficiency-aware `_proj` extractor or `_proj`
> rank-polynomial in tree** — `_le_finrank` is full-span-only, `_proj` is rigid-only. No `.lean`/`.tex` edits
> this pass.

**Citation.** Katoh–Tanigawa 2011, *Discrete Comput. Geom.* **45**, 647–700; **Lemma 6.3**, §6.2, p. 673
(the simple Case-I arm `case_I_realization` restates), with the `k > 0` surviving-block rank routed through
**Lemma 5.1** (the [29] White–Whiteley pin-a-body fact, p. 668, landed as `finrank_pinnedMotions_add_screwDim`),
exactly as §1.64 settled for the non-simple (Lemma 6.2) arm.

**(a) What the row-104 BLOCK got right (re-verified) and what it under-specified.** The BLOCK's structural
diagnosis is **correct and confirmed against the landed source**: `case_I_realization`'s surviving block routes
through the rigid `rigidContract_exterior_rank_transport` (CaseI:1682, `hdef = 0` at :1684) +
`exists_rankPolynomial_of_rigidOn_linking_set_proj` (CaseI:1506), both unavailable at the deficient (`k > 0`)
contraction, *and* the final rigid coupler
`hasGenericFullRankRealization_of_couple_blockTriangular_ofNormals_set` (CaseI:1988) is doubly `0`-dof-gated
(hard `hdef = 0` at :2013, plus its `hsc_proj_indep` demands the *full* `D(|sc|−1)` projected surviving rank at
:2010, not `D(|sc|−1) − k`). So the all-`k` simple restate cannot thread the landed proof with `k` for `0`; it
needs a different surviving-block route. The BLOCK named two candidate routes but did not pin a signature or
rate the difficulty; that is this pass's job. **What the BLOCK under-specified:** it framed the wall purely as
"control `finrank (Dmap '' Fsurvive)` at a fresh generic seed" via the degenerate-placement-only
`panelRow_collapseTo_comp_extProj_dualMap` — but the landed **L5a-ii** machinery (`hInj` +
`hingeRow_collapseTo_comp_extProj_eq`, both placement-free) already sidesteps the per-edge `panelRow`
correspondence for the *brick's* purposes; the genuine residual gap is narrower and sharper than the BLOCK
stated (see (c)).

**(b) The target shape — `case_I_realization_all_k` follows the L4b-2 GP-builder pattern, NOT the rigid
`case_I_realization` coupler.** The all-`k` simple Case I is the **splice analogue of the landed
`case_cut_edge_realization_gp`** (L4b-2, CaseI:8108), the all-`k` GP cut producer. That pattern, verified
against the landed L4b-2 proof, is: (1) the IH gives the relevant smaller-graph realizations at their *deficient*
ranks; (2) per-leg deficiency-aware **rank polynomials** (`exists_rankPolynomial_of_le_finrank_linking`,
L4b-1) transfer each leg's rank to *any* non-root seed; (3) a single **fresh combined alg-indep seed `q₀`**, a
non-root of `Q_H · Q_surv · Q_gp`, is chosen; (4) at `q₀`, the single framework `F = ofNormals G G.endsOf q₀`
is general position and each block reaches its deficient rank; (5) a **block-rank brick** (L4a's
`_of_cut` for the cut case → L5a-i's `_of_splice` for the splice case) lower-bounds `finrank (span F.rigidityRows)`
by the block sum; (6) **B2** (`finrank_span_rigidityRows_add_deficiency_le`, the free `≤`) closes the M2 rank
equality by antisymmetry. This is *not* the rigid `case_I_realization` route (which reads rigidity off a row
count and only works at full rank `D(|V|−1)`, `def = 0`); it is the project's standing all-`k` GP-producer
idiom, which already exists for the cut case. The L5a-i splice brick was *built general-rank precisely so this
pattern transfers* — its `hFH_le`/`hFH_ker`/`hFc_surv_le`/`hInj` interface is `D`-abstract and rigidity-free.

**(c) The genuine residual gap — the V6-b leaf — pinned and rated `P≈3` (a real brick, not assembly).**
Threading the L4b-2 pattern through the splice brick, the H-leg and the brick assembly are clean reuses of
landed pieces (the rigid H-block rank polynomial `exists_rankPolynomial_of_rigidOn_linking_set` works — `H` is a
*rigid* proper subgraph; the `hInj` is the landed L5a-ii kernel; `hFH_le`/`hFH_ker` mirror the non-simple
producer's; B2 is free). The **one** piece with no landed precedent is the **surviving-block rank input to the
brick at the fresh generic seed**, i.e. discharging `Fc` (the contraction framework the brick reads) with both:
(i) `finrank (span Fc.rigidityRows) ≥ D(|sc|−1) − k`, and (ii) `hFc_surv_le : (span Fc.rigidityRows).map Dmap ≤
(span F.rigidityRows).map Dmap`, **simultaneously at a single seed compatible with `F = ofNormals G G.endsOf q₀`.**

This is genuinely new because of the **collapsed/uncollapsed normal mismatch crossed with deficiency**:
- For `hFc_surv_le` to discharge via the placement-free `hingeRow_collapseTo_comp_extProj_eq` (the non-simple
  producer's route, CaseI:8645), `Fc` must be a contraction framework whose surviving extensors are the
  *pulled-back* `q₀`-extensors — i.e. `Fc = (ofNormals (G.rigidContract H r) endsᶜ (degeneratePlacement r V(H)
  q₀)).toBodyHinge`, where `endsᶜ` is the relabel selector and `degeneratePlacement` (CaseI:907) is the
  collapsed-normal field `a ↦ q₀(collapseTo r V(H) a)`. (On surviving edges with an endpoint inside `V(H)∖{r}`
  the extensor genuinely *differs* from `F`'s, which is why the reconciliation must happen *after* `Dmap`, not
  as an extensor equality — exactly the non-simple producer's mechanism.)
- But this `Fc` is at a **degenerate placement** (the `V(H)` normals coincide), so its rank is *not* the IH's
  `D(|sc|−1) − k` for free — the IH delivers that rank only at the contraction's *own generic* seed `Qc`. The
  deficiency-aware full-span rank polynomial `exists_rankPolynomial_of_le_finrank_linking` (L4b-1) transfers the
  IH rank from `Qc`'s seed to *a non-root contraction seed* — but `degeneratePlacement r V(H) q₀` is a *specific
  function of `q₀`* (the pin's outer variable), not a free contraction seed, so the rank polynomial cannot be
  evaluated at it directly. The rigid route bridges this exact gap with U3a
  (`hasGenericRealization_transport_relabel`, **`hdef = 0`-gated**) → U3b (the rigid `_proj` extractor) → U2 →
  the rigid `_proj` rank polynomial; **the deficient analogue of every link in that chain is missing from the
  tree** (W6e `_le_finrank` is full-span-only; the `_proj` extractor and `_proj` rank polynomial are rigid-only;
  `hasGenericRealization_transport_relabel` needs `hdef = 0`). Discharging (i)+(ii) at a single `q₀`-compatible
  seed is therefore the deficient (`_le_finrank`) reconstruction of the U3a/U3b/U2-proj + rank-polynomial-proj
  chain — a multi-lemma brick, **not a one-call assembly**. **Rated `P≈3`** (genuinely-new linear algebra
  needing its own brick / small family), the same tier as the L5a-i brick.

The math is *settled* (KT Lemma 5.1 + the block-triangular argument; the pieces are all rigidity-free in
principle) and **needs NO motive / IH statement-level change** — but the **internal route is a flagged open
design decision** for the V6-b build, because the two candidate decompositions are genuinely different and the
choice is best made with the actual goal state in hand:

* **Route 1 (projected rank-transport, the BLOCK's route (1)).** Build the deficiency-aware analogue of
  `rigidContract_exterior_rank_transport` + `exists_rankPolynomial_of_rigidOn_linking_set_proj`: a rank
  polynomial `Q_proj` over the original-graph selector whose non-roots give `D(|sc|−1) − k` *exterior-projected*
  independent surviving rows of `ofNormals G G.endsOf q`. This feeds the brick's surviving block directly (no
  separate `hInj` — the projection independence *is* the rank). New lemmas: a deficiency-aware `_proj` extractor
  (the `_le_finrank` analogue of `exists_independent_panelRow_subfamily_of_rigidOn_linking_set_proj`) + a
  deficiency-aware `_proj` rank polynomial (the `_le_finrank` analogue of
  `exists_rankPolynomial_of_rigidOn_linking_set_proj`) + a deficiency-aware relabel transport (the `hdef`-free
  analogue of `hasGenericRealization_transport_relabel`). **Pro:** mirrors the landed rigid chain step-for-step
  (easiest to verify against KT's own argument). **Con:** rebuilds three GenericityDevice lemmas.
* **Route 2 (pulled-back full-span + the landed `hInj`).** Use the *landed* L5a-ii `hInj`
  (`finrank Sc = finrank (Sc.map Dmap)`) on the pulled-back `Fc` so the brick's `hInj` is free, then supply
  `finrank Sc ≥ D(|sc|−1) − k` via the *full-span* deficiency-aware rank polynomial `exists_rankPolynomial_of_le_finrank_linking`
  (L4b-1, **already in tree**). **Pro:** reuses the landed `hInj` and the landed L4b-1 full-span rank polynomial
  — fewer new lemmas. **Con:** still needs the deficiency-aware relabel transport to put the IH rank onto the
  *pulled-back* (`degeneratePlacement q₀`) seed before the full-span rank polynomial can carry it to `q₀`; the
  `q₀`-dependence of `degeneratePlacement r V(H) q₀` is the same bridge route 1 builds inside its `_proj`
  transport. So route 2 trades two `_proj` lemmas for one full-span lemma but does **not** eliminate the
  relabel-transport core.

**Decision (flagged, for coordinator/user adjudication if desired; otherwise resolved at the V6-b build):** both
routes need a **deficiency-aware relabel-and-extract transport** as their irreducible new content; route 2 then
reuses two landed pieces (`hInj` + L4b-1) where route 1 rebuilds two `_proj` siblings. **Recommend route 2** as
the smaller new surface (it leans on the L5a-ii / L4b-1 work just landed), but the recommendation is *soft* — the
relabel-transport's exact statement (what rank invariant it carries across the collapse at general rank) is the
real uncertainty, and it should be pinned with the goal state open, not committed here. This is the honest
analogue of the §1.64(c) flag, one tier sharper: §1.64 said "buildable, its own slice"; this says "buildable, its
own slice, **and the slice's internal proof structure is an open decision** — do not over-commit it in a pin."

**(d) The V6-b leaf signature (the new brick) — pinned by interface, internal route deferred.** Stated as the
surviving-block rank input the splice brick consumes at the fresh seed. The exact form depends on the route (c);
the **interface** (what `case_I_realization_all_k` needs from it) is route-independent:

```lean
/-- **Deficiency-aware exterior-projected surviving-block rank transport** (the V6-b leaf;
KT Lemma 6.3 at `def = k > 0`, the `_le_finrank` analogue of `rigidContract_exterior_rank_transport`
+ `exists_rankPolynomial_of_rigidOn_linking_set_proj`; Phase 22i L5b). For the surviving-edge
subgraph `G ＼ E(H)` and a proper rigid subgraph `H ≤ G` with representative `r`, whose contraction
`G.rigidContract H r` is realized by the IH at the deficient rank `D(|sc|−1) − k` (`sc = (V(G)∖V(H))∪{r}`),
there is a nonzero rational polynomial `Q` over the original-graph selector such that at every
`Q`-non-root seed `q`, the `(extProj V(H)).dualMap`-projected surviving rows of `ofNormals (G ＼ E(H))
ends q` reach rank `≥ screwDim k * (sc.ncard - 1) - k`. -/
theorem PanelHingeFramework.exists_rankPolynomial_surviving_proj_of_le_finrank
    [Finite α] [Finite β] (G H : Graph α β) (ends : β → α × α) {r : α}
    (hr : r ∈ V(H)) (hHsub : V(H) ⊆ V(G)) {n : ℕ} {k : ℤ}
    (hHproper : H.IsProperRigidSubgraph G n)
    (hKmin : (G.rigidContract H r).IsMinimalKDof n k)
    (hFc : HasPanelRealization (k := 2) n (G.rigidContract H r))   -- or the GP IH, per route
    (… selector / transversality hyps mirroring `exists_rankPolynomial_of_rigidOn_linking_set_proj` …) :
    ∃ Q : MvPolynomial (α × Fin (2 + 2)) ℝ, Q ≠ 0 ∧
      (Q.coeffs : Set ℝ) ⊆ Set.range (algebraMap ℚ ℝ) ∧
      ∀ q : α × Fin (2 + 2) → ℝ, MvPolynomial.eval q Q ≠ 0 →
        screwDim 2 * ((((V(G) \ V(H)) ∪ {r}).ncard : ℤ) - 1) - k ≤
          Module.finrank ℝ (Submodule.span ℝ
            ((extProj (k := 2) V(H)).dualMap.??? …))   -- the projected surviving-row span at q
```
The `(…)` and the `???` are **deliberate design slots** (this is a *pin*, not a build): the conclusion's exact
shape (projected-rows-rank for route 1; or split into `finrank Sc ≥ D(|sc|−1)−k` over a pulled-back `Fc` + the
landed `hInj` + `hFc_surv_le` for route 2) is the (c) open decision. Whichever route, the *interface* the
producer needs is "a `Q`-non-root seed gives the surviving block its deficient rank `D(|sc|−1) − k` under the
exterior projection" — the deficient sibling of the rigid coupler's `hsc_proj_indep` premise (CaseI:2006), with
the rank lowered from `D(|sc|−1)` to `D(|sc|−1) − k` and the independence weakened to a rank `≥`.

**(e) The all-`k` GP producer `case_I_realization_all_k` (the assembly that consumes the V6-b leaf).** Mirrors
`case_cut_edge_realization_gp` (L4b-2) with the splice brick. The signature (all-`k`, the conditioned-pair IH
the L9 spine threads, the simple branch concluding the GP conjunct):
```lean
theorem case_I_realization_all_k [DecidableEq β] [Finite α] [Finite β] {n : ℕ}
    (hD : 2 ≤ Graph.bodyBarDim n) (hn : Graph.bodyBarDim n = screwDim 2)
    {k : ℤ} (G : Graph α β) (hG : G.IsMinimalKDof n k) (_hV3 : 3 ≤ V(G).ncard)
    (hSimple : G.Simple) {H : Graph α β} (hH : H.IsProperRigidSubgraph G n) {r : α} (hr : r ∈ V(H))
    (hcSimple : (G.rigidContract H r).Simple)
    (hIH : ∀ (k' : ℤ) (G' : Graph α β), G'.IsMinimalKDof n k' → V(G').Nonempty →
      V(G').ncard < V(G).ncard →
      (G'.Simple → PanelHingeFramework.HasGenericFullRankRealization 2 n G') ∧
        HasPanelRealization 2 n G') :
    PanelHingeFramework.HasGenericFullRankRealization 2 n G
```
Body: H-leg rigid rank polynomial (`exists_rankPolynomial_of_rigidOn_linking_set`, `H` is rigid) + the **V6-b
leaf** for the surviving block + `exists_generalPosition_polynomial`; fresh combined alg-indep seed `q₀` a
non-root of all three; `F := ofNormals G G.endsOf q₀`; the L5a-i splice brick `le_finrank_span_rigidityRows_of_splice`
gives the block-sum `≥`; B2 the `≤`; antisymmetry closes the M2 rank at `D(|V|−1) − k`. **The 6.5 sub-arm
stays red → L8** (this producer is the 6.3 arm only; it takes `hcSimple` as the dispatch's positive-branch
output, exactly as the landed `theorem_55_d3` Case-I dispatch hands `case_I_realization` its `hcSimple` at
:7557). Statement change vs the landed `case_I_realization` → grep `blueprint/src` per the structural-edit gate
before committing the restate.

**(f) The `hcontract` dispatch (the §1.63(a) `by_cases G.Simple`, all-`k`).** The final assembly that fills L9's
`hcontract` slot. Unchanged in shape from §1.63(a) / the landed `theorem_55_d3` `hcontractGP` dispatch
(:7552–7561), restated all-`k`: `by_cases G.Simple` → simple branch dispatches on whether some proper rigid
subgraph has a simple contraction (the landed 6.3-vs-6.5 `by_cases hd`), positive → `case_I_realization_all_k`,
negative → the `h65` carry; non-simple → the landed `case_I_realization_nonsimple` (L5a-ii). This is **plumbing**
(no new math) once `case_I_realization_all_k` lands — but per `CLAUDE.md` *"wiring is a deliverable"*, it is its
own checklist leaf, not a commit-message phrase.

**(g) The re-cut L5b slice (exact build leaves, build order).** Three leaves, the V6-b brick first:

* **L5b-i** — the **V6-b leaf** (d): `exists_rankPolynomial_surviving_proj_of_le_finrank` (or its route-2
  split) in GenericityDevice.lean / CaseI.lean. **`P≈3` — the one genuinely-new math of L5b, its own slice, the
  first concrete L5b commit.** The (c) route decision (route-1 `_proj` mirror vs route-2 pulled-back full-span +
  `hInj`) resolves at this build with the goal state open. If it won't fit one sitting, the deficiency-aware
  relabel transport (the shared core of both routes) splits out as its own sub-commit. **Flagged: do not pin the
  internal route in advance — both candidates are live and the relabel-transport's exact rank invariant is the
  real uncertainty.**
* **L5b-ii** — `case_I_realization_all_k` (e): the GP producer, the splice-brick analogue of L4b-2's
  `case_cut_edge_realization_gp`. Assembly of landed pieces + the L5b-i leaf. **`P≈2`** (a clean assembly once
  the leaf lands, mirroring a landed producer). Statement change → blueprint statement-grep gate. Mints
  `lem:case-I-realization-all-k`.
* **L5b-iii** — the `hcontract` slot-filler dispatch (f): `by_cases G.Simple` wiring. **`P≈1`** (plumbing).
  Updates `lem:case-I-dispatch`. Completes the full `Pc` slot-filler `⟨gp, bare⟩`; the `h65` sub-arm stays red
  → L8.

*Verification items L5b resolves:* **V6-b RESOLVED at the pin level (this pass) — re-rated `P≈3`** (NOT the
§1.64(f) "buildable, GP variant" understatement, which read as `P≈2`): it is a real new brick, the deficient
reconstruction of the rigid U3a/U3b/U2-proj + rank-polynomial-proj chain, with a flagged internal-route decision.
The V6-b *build* (L5b-i) is where the route decision lands; the producer (L5b-ii) and dispatch (L5b-iii) are then
assembly + plumbing.

### 1.66 The L5b-ii route resolution — `hFc_surv_le` is a DEAD END for the GP simple producer (the splice brick is the wrong vehicle, not a discharge gap): route 1 (`_proj`-coupler mirror) is the only viable route, route 2's L5b-i leaf `exists_rankPolynomial_of_IH_relabel_linking` is SUPERSEDED (dead, no consumer — leave harmless); the all-`k` simple Case I must mirror the LANDED rigid `case_I_realization` (the block-triangular row-counting coupler `hasGenericFullRankRealization_of_couple_blockTriangular_ofNormals_set`, NOT `le_finrank_span_rigidityRows_of_splice`), so the V6-b leaf is re-pinned as the deficient `_proj` surviving-row independence the coupler's `hsc_proj_indep` consumes; no motive/IH change; re-decomposed L5b-ii → three buildable leaves (2026-06-13)

> **Docs-only design pass, every load-bearing decl re-verified against the LANDED Lean this pass** (the
> §1.65 soft-rec for route 2 + the BLOCK both came from prose-trust; this pass opened each `def`/`theorem`
> and traced the *mechanism*, not the conclusion). Decls read end-to-end:
> RigidityMatrix.lean — `le_finrank_span_rigidityRows_of_splice` (:3213, the L5a-i splice brick, four hyps
> incl. `hFc_surv_le : (span Fc.rows).map D ≤ (span F.rows).map D` at :3218); `hingeRowBlock` (:754,
> `= (span {F.supportExtensor e})^⊥`); `rigidityRows` (:920, `{hingeRow u v r | F.graph.IsLink e u v, r ∈
> hingeRowBlock e}`); `hingeRow` (:807, `r ∘ₗ screwDiff u v` — depends only on `u,v,r`). CaseI.lean —
> `case_I_realization_nonsimple` (:8610, the **bare** producer; its `hFc_surv_le` discharge :8776–8804 is
> the load-bearing precedent — the `hr'F : r' ∈ F.hingeRowBlock e'` step at :8792 relies on `hextEq : extF
> e' = Fc_fw.supportExtensor e'` at :8791, i.e. **support-extensor equality on surviving edges**; `F`
> hand-built to copy `Fc`'s extensors at :8712–8725, concludes only the bare motive); `case_I_realization`
> (:2360, the rigid `def=0` simple Lemma-6.3 arm — routes through the coupler `..._couple_blockTriangular_ofNormals_set`
> at :2529, NOT through the splice brick); `hasGenericFullRankRealization_of_couple_blockTriangular_ofNormals_set`
> (:2119, the coupler — its `hsc_proj_indep` at :2137 demands the surviving rows be `(extProj sH).dualMap`-
> independent of size `≥ D(|sc|−1)` as panel rows of **`F = ofNormals G ends q₀`** at :2143, never a span-
> containment); `rigidContract_exterior_rank_transport` (:1813, `hdef=0` at :1815, converts the IH to
> rigidity `hQrig` at :1843); `..._htransport` producer (:1903, `hdef=0` at :1905; output seed is
> `degeneratePlacement r V(H) nrm'` at :1986); `exists_independent_panelRow_subfamily_of_rigidOn_linking_set_proj`
> (:1259, the rigid `_proj` extractor, `hrig` at :1264, routes through `injOn_extProj_dualMap_rigidityRows`
> at :1292 — **full-rigidity-gated**); `hasGenericRealization_transport_relabel` (:1371, U3a, `hdef` gate);
> `injOn_extProj_dualMap_rigidityRows_of_inter_eq_singleton` (:1176, **rigidity-FREE** injOn core, the L5a-ii
> landing) + `finrank_span_rigidityRows_map_extProj_dualMap_of_inter_eq_singleton` (:1209, the `hInj` form);
> `finrank_span_rigidityRows_ofNormals_relabel_eq` (:1447, the L5b-i shared core, **rigidity-free** relabel
> rank-equality transport); `exists_rankPolynomial_of_IH_relabel_linking` (:1511, the L5b-i **route-2 leaf** —
> output is the **full-span** rank of `ofNormals (Gc.map f) endsᵐ q`, i.e. `Fc`'s rows, the splice brick's
> input); `panelRow_collapseTo_comp_extProj_dualMap` (:940, U2, the per-edge correspondence AT
> `degeneratePlacement r V(H) nrm`, rigidity-free); `degeneratePlacement` (:907); `extProj` (:821),
> `hingeRow_comp_extProj_eq_zero` (:862), `hingeRow_collapseTo_comp_extProj_eq` (:884).
> GenericityDevice.lean — `exists_independent_panelRow_subfamily_of_le_finrank` (:718, W6e, the
> deficiency-aware UNprojected `panelRow` extractor) + `exists_rankPolynomial_of_le_finrank_linking` (the
> L4b-1 full-span rank polynomial). PanelHinge.lean — `HasGenericFullRankRealization` (:1035, demands
> `Q.IsGeneralPosition` + `Q.graph = G`) + `toBodyHinge_supportExtensor` (:95, `= panelSupportExtensor
> (normal (ends e).1) (normal (ends e).2)`) + `ofNormals` (:253, `normal a i = q(a,i)`). **CaseI builds green
> (exit 0) at HEAD `6d74065`.** No `.lean`/`.tex` edits this pass.

**Citation.** Katoh–Tanigawa 2011, *Discrete Comput. Geom.* **45**, 647–700; **Lemma 6.3** §6.2 p. 673 (the
simple Case-I arm), the `def = k > 0` surviving-block rank routed through **Lemma 5.1** (White–Whiteley pin-a-body,
p. 668; landed as `finrank_pinnedMotions_add_screwDim` / its corank consequence the rigidity-free `injOn` core).

**(a) The decisive finding — `hFc_surv_le` is undischargeable for the GP producer because it is the WRONG
mechanism, not a missing lemma.** Trace the non-simple producer's `hFc_surv_le` discharge (CaseI:8776–8804) to
its load-bearing step. For each `Fc`-row `hingeRow (f u)(f v) r'` (collapsed surviving link, `r' ∈ Fc.hingeRowBlock
e'`), the proof needs `hingeRow u v r' ∈ F.rigidityRows`, which needs `r' ∈ F.hingeRowBlock e'`. Since
`hingeRowBlock e = (span {supportExtensor e})^⊥` (RigidityMatrix:754), `r' ∈ Fc.hingeRowBlock e' ⟹ r' ∈
F.hingeRowBlock e'` holds **iff `F.supportExtensor e'` is parallel to `Fc.supportExtensor e'`** — the non-simple
producer gets this *for free* because it hand-builds `F` to **copy** `Fc`'s extensor on surviving edges (`extF e'
= Fc_fw.supportExtensor e'`, CaseI:8723–8725) and concludes only the **bare** motive. The `hingeRow_collapseTo_comp_extProj_eq`
reconciliation handles only the *endpoint* relabel `(f u, f v) → (u, v)` after `Dmap`; it does **nothing** for the
hinge-row *block* (the support-extensor dependency).

The GP conjunct `HasGenericFullRankRealization` (PanelHinge:1035) forces `F = (ofNormals G G.endsOf q₀).toBodyHinge`
at a fixed seed, so `F.supportExtensor e' = panelSupportExtensor (q₀ u)(q₀ v)` (PanelHinge:95). For a **crossing
edge** `e'` of `H` that survives (one endpoint `u ∈ V(H)∖{r}`, the other `v ∉ V(H)`, `e' ∉ E(H)` — these exist
whenever `H` has boundary edges, the generic Case-I situation; `rigidContract` keeps them and redirects `u → r`),
*every* contraction framework `Fc` has `Fc.supportExtensor e' = panelSupportExtensor (Fc-nrm r)(Fc-nrm v)` (the
collapsed normal at `r`, not `u`). `panelSupportExtensor (q₀ u)(q₀ v)` and `panelSupportExtensor (q₀ r)(q₀ v)` are
extensors of **different point-pairs** (`u` vs `r`), generically **non-parallel**. So `hFc_surv_le`'s discharge
step `r' ∈ Fc.hingeRowBlock e' ⟹ r' ∈ F.hingeRowBlock e'` **fails for the GP `F`** — not for want of a lemma, but
because the two frameworks genuinely disagree on the surviving-edge hinge constraints when `F` is pinned to a
clean seed. **The splice brick is the non-simple producer's vehicle (bare motive, `F` copies `Fc`); it is the
wrong vehicle for the GP producer.** Both the BLOCK's "discharge `hFc_surv_le` at a degenerate seed" and §1.65's
route-2 soft-rec mis-framed the obstacle as a discharge gap; it is a **mechanism mismatch**.

**(b) Why route 2 cannot be repaired by a degenerate seed (the BLOCK's candidate (2) is unsound for the
producer).** The BLOCK proposed: realize `Fc` at `degeneratePlacement r V(H) q₀` so `hingeRow_collapseTo_comp_extProj_eq`
discharges `hFc_surv_le`, then show the L5b-i polynomial `Q` is nonzero there. But `hFc_surv_le`'s *real*
requirement (a) is support-extensor parallelism between `F` and `Fc` on surviving edges — and at the degenerate
placement `Fc-nrm = q₀ ∘ collapseTo r V(H)`, so `Fc.supportExtensor e' = panelSupportExtensor (q₀ r)(q₀ v)` on a
crossing edge, which is *still* not parallel to `F`'s `panelSupportExtensor (q₀ u)(q₀ v)`. Realizing `Fc` at the
degenerate placement does not change the obstruction — the only way to make `F`'s and `Fc`'s extensors agree is to
hand-build `F` to copy `Fc` (the non-simple route), which **forfeits the GP conjunct** (`F` is then no longer
`ofNormals G G.endsOf q₀` and is not in general position on crossing-edge endpoints). Route 2 is a genuine dead
end for L5b-ii.

**(c) The viable route — route 1, the `_proj`-coupler mirror, which is the deficiency-aware twin of the LANDED
rigid `case_I_realization`.** The rigid `case_I_realization` (CaseI:2360) — the very lemma the all-`k` simple arm
restates — **does not use the splice brick at all.** It routes through the block-triangular coupler
`hasGenericFullRankRealization_of_couple_blockTriangular_ofNormals_set` (CaseI:2119), which exhibits `D(|V|−1)`
independent rigidity rows of the *single* framework `F = ofNormals G ends q₀` itself: the H-block rows (which
vanish under `Dmap = (extProj sH).dualMap`, KT's top-right `0`) `⊔` the **exterior-projected** surviving rows
(KT's bottom-right block). The surviving block enters as `hsc_proj_indep` (CaseI:2137): a rank-polynomial-gated
witness that, at the seed, `F`'s **own** surviving panel rows are `(extProj V(H)).dualMap`-independent of size `≥
D(|sc|−1)`. This is a statement about `F`'s rows projected away from the rigid columns — **never** a span-
containment `Fc.rows.map D ≤ F.rows.map D`. The coupler never needs `Fc.supportExtensor = F.supportExtensor`
because it reads everything off `F`. **This is the route the deficient case must mirror** (lowering the projected
rank target from `D(|sc|−1)` to `D(|sc|−1) − k` and weakening "independent" to "rank `≥`").

The rigid chain feeding `hsc_proj_indep` is `rigidContract_exterior_rank_transport` (CaseI:1813, `hdef=0`) →
`..._htransport` (CaseI:1903) → U3a `hasGenericRealization_transport_relabel` (`hdef`-gated) + U3b
`exists_independent_panelRow_subfamily_of_rigidOn_linking_set_proj` (CaseI:1259, `hrig`-gated, routes through
`injOn_extProj_dualMap_rigidityRows`) + U2 `panelRow_collapseTo_comp_extProj_dualMap` (CaseI:940, at the
degenerate seed), packaged as `exists_rankPolynomial_of_rigidOn_linking_set_proj`. The output seed is itself the
degenerate placement `degeneratePlacement r V(H) nrm'` (CaseI:1986); the rank polynomial then carries the
projected independence from that degenerate witness to any fresh non-root seed — **the degenerate placement plays
its role inside the rank-polynomial construction, exactly as KT intends, and the producer's fresh combined seed is
a non-root, never the degenerate point.** This dissolves the BLOCK's "seed conflict": the degenerate placement is
the *witness* the rank polynomial is built at, not the seed the producer realizes at.

**The deficient analogues of every `hdef=0`/`hrig` link are already landed or near-mechanical** (this is why route
1 is `P≈3`, a real brick, not research-shaped):
- U3a (`hasGenericRealization_transport_relabel`, `hdef`-gated) → the **landed** L5b-i shared core
  `finrank_span_rigidityRows_ofNormals_relabel_eq` (CaseI:1447): carries the contraction IH's rank
  `D(|V(Gc.map f)|−1) − def` across the *same* collapse-relabel swap, rigidity-free, as a finrank equality. **This
  is the one piece §1.65(c) flagged as the real uncertainty, and it is already in tree** (it landed for route 2,
  but route 1 reuses it — see (d)).
- U3b's `injOn` core (`injOn_extProj_dualMap_rigidityRows`, `hrig`-gated) → the **landed** L5a-ii
  `injOn_extProj_dualMap_rigidityRows_of_inter_eq_singleton` (CaseI:1176, rigidity-free, needs only
  `V(Fc.graph) ∩ V(H) = {r}`).
- U3b's un-projected extractor (`exists_independent_panelRow_subfamily_of_rigidOn_linking`, `hrig`-gated) → the
  **landed** W6e `exists_independent_panelRow_subfamily_of_le_finrank` (GenericityDevice:718, rank-input form).
- U2 `panelRow_collapseTo_comp_extProj_dualMap` (CaseI:940) is **already rigidity-free** — reused verbatim.
- The genuinely-new step is the **deficient `_proj` extractor** = W6e `_le_finrank` un-projected extractor
  composed with the rigidity-free `injOn` core (mirroring how the rigid `_proj` extractor CaseI:1259 composes the
  rigid un-projected extractor with the rigid `injOn` at :1292), then packaged as a **deficient `_proj` rank
  polynomial** mirroring `exists_rankPolynomial_of_rigidOn_linking_set_proj`. This is ~2 new GenericityDevice/CaseI
  lemmas, the `_le_finrank` siblings of the two rigid `_proj` tools — a real but bounded brick.

**No motive / IH statement-level change.** Route 1 produces the same `HasGenericFullRankRealization` conclusion
through the same coupler the rigid arm uses; only the surviving-block rank input is deficiency-aware. The honest
flag (§1.64(c)/§1.65(c)) stands at one tier: the deficient `_proj` chain is genuinely-new linear algebra (its own
slice), but the math is settled (KT Lemma 5.1 + block-triangular) and every link is either landed or a near-
mechanical `_le_finrank` mirror of a landed `_proj` tool.

**(d) Disposition of the landed L5b-i route-2 pieces.** Two decls landed for route 2:
- `finrank_span_rigidityRows_ofNormals_relabel_eq` (the shared core, CaseI:1447) — **REUSED by route 1** as its
  U3a relabel-transport analogue. **Keep.** (It is the rigidity-free relabel rank-equality both routes need; route
  1's deficient `_proj` extractor reads the contraction's rank from it.)
- `exists_rankPolynomial_of_IH_relabel_linking` (the route-2 leaf, CaseI:1511) — produces the **full-span** rank of
  `ofNormals (Gc.map f) endsᵐ q` (the contraction framework `Fc`'s rows), the input the **splice brick** consumes.
  Route 1 does not use the splice brick, so this leaf is **SUPERSEDED (dead) for L5b**. Verified: it has **no
  consumer** in tree (grep: only its own `theorem` + the shared-core call it makes). **Recommendation: leave it
  harmless** for now (it is axiom-clean, build-green, and its `lem:rank-polynomial-IH-relabel` blueprint node is a
  truthful statement of a real fact) and delete it at the L5b close once route 1 has landed and confirmed it is not
  resurrected — deleting it now would also strand its green blueprint node mid-build. Flag it in the L5b-i checklist
  as "route-2 leaf, superseded by §1.66 route 1, delete-at-close candidate". (Its shared-core dependency
  `lem:rank-transport-relabel-of-le-finrank` survives — route 1 uses it.)

**(e) The V6-b leaf re-pinned for route 1 (the deficient `_proj` surviving-row independence).** The interface the
coupler's `hsc_proj_indep` consumes, deficiency-aware. Two new decls (the `_le_finrank` siblings of the rigid
`_proj` pair):
```lean
/-- **Deficiency-aware exterior-projected independent surviving subfamily** (the V6-b leaf, route-1 extractor;
the `_le_finrank` analogue of `exists_independent_panelRow_subfamily_of_rigidOn_linking_set_proj`, swapping the
rigidity gate for a rank input + the rigidity-free `injOn` core; Phase 22i L5b-i). -/
theorem BodyHingeFramework.exists_independent_panelRow_subfamily_of_le_finrank_proj
    [Finite α] [Finite β] (F : BodyHingeFramework k α β) {ends : β → α × α} {proj : Set α} {r : α}
    (hends : ∀ e u v, F.graph.IsLink e u v → F.graph.IsLink e (ends e).1 (ends e).2)
    (hne : ∀ e, F.graph.IsLink e (ends e).1 (ends e).2 → F.supportExtensor e ≠ 0)
    (hinter : F.graph.vertexSet ∩ proj = {r})       -- the rigidity-free injOn input (L5a-ii)
    {N : ℕ} (hN : N ≤ Module.finrank ℝ (Submodule.span ℝ F.rigidityRows)) :   -- rank input, not hrig
    ∃ t : Set (β × Set.powersetCard (Fin (k + 2)) k × Set.powersetCard (Fin (k + 2)) k),
      (∀ i ∈ t, F.graph.IsLink (i : β × _ × _).1 (ends (i : β × _ × _).1).1 (ends (i : β × _ × _).1).2) ∧
      N ≤ Nat.card t ∧
      LinearIndependent ℝ (fun i : t => (extProj (k := k) proj).dualMap (F.panelRow ends (i : β × _ × _)))
-- Proof: the rigid extractor's body verbatim with `hrig`→`hN` (call W6e `_le_finrank` instead of the rigid
-- un-projected extractor) and `injOn_extProj_dualMap_rigidityRows hrig hr hinter`→
-- `injOn_extProj_dualMap_rigidityRows_of_inter_eq_singleton hinter` (the L5a-ii rigidity-free core).
```
```lean
/-- **Deficiency-aware `_proj` rank polynomial** (the V6-b leaf, route-1 polynomial; the `_le_finrank` analogue of
`exists_rankPolynomial_of_rigidOn_linking_set_proj`; Phase 22i L5b-i). From the contraction IH on `Gc.map f`,
produces a nonzero rational `Q` whose non-roots give the coupler's `hsc_proj_indep`: at every `Q`-non-root seed
`q`, the `(extProj V(H)).dualMap`-projected surviving rows of `ofNormals Gc ends q` are independent of size
`≥ D(|sc|−1) − k`. -/
theorem PanelHingeFramework.exists_rankPolynomial_of_IH_relabel_linking_set_proj
    [Finite α] [Finite β] (G H : Graph α β) (ends : β → α × α) {r : α}
    (hr : r ∈ V(H)) (hHsub : V(H) ⊆ V(G)) {n : ℕ} {k' : ℤ}
    (hKmin : (G.rigidContract H r).IsMinimalKDof n k')
    (hQcf : PanelHingeFramework.HasGenericFullRankRealization 2 n (G.rigidContract H r))
    (hcLoop : (G.rigidContract H r).Loopless)
    (hends : ∀ e u v, (G.deleteEdges E(H)).IsLink e u v →
      (G.deleteEdges E(H)).IsLink e (ends e).1 (ends e).2) :
    ∃ Q : MvPolynomial (α × Fin (2 + 2)) ℝ, Q ≠ 0 ∧ (Q.coeffs : Set ℝ) ⊆ Set.range (algebraMap ℚ ℝ) ∧
      ∀ q : α × Fin (2 + 2) → ℝ, MvPolynomial.eval q Q ≠ 0 →
        ∃ t : Set (β × Set.powersetCard (Fin 4) 2 × Set.powersetCard (Fin 4) 2),
          (∀ i ∈ t, (G.deleteEdges E(H)).IsLink (i : β × _ × _).1
            (ends (i : β × _ × _).1).1 (ends (i : β × _ × _).1).2) ∧
          screwDim 2 * (((V(G) \ V(H)) ∪ {r}).ncard - 1) - k' ≤ (Nat.card t : ℤ) ∧
          LinearIndependent ℝ (fun i : t => (extProj (k := 2) V(H)).dualMap
            ((PanelHingeFramework.ofNormals (G.deleteEdges E(H)) ends q).toBodyHinge.panelRow
              ends (i : β × _ × _)))
-- Proof: mirror `rigidContract_exterior_rank_transport_htransport` (CaseI:1903) at the deficient leg —
-- the shared core `finrank_span_rigidityRows_ofNormals_relabel_eq` (landed) gives the relabel-leg framework
-- `F' = ofNormals (Gc.map f) endsᵐ nrm` with finrank = `D(|sc|−1) − k'`; feed that rank to the new `_proj`
-- extractor above (proj = V(H)); U2 `panelRow_collapseTo_comp_extProj_dualMap` (CaseI:940, landed, rigidity-
-- free) carries the projected independence from the relabel leg to `ofNormals Gc ends (degeneratePlacement
-- r V(H) nrm')`; then `exists_rankPolynomial_of_le_finrank_linking`-style packaging (L4b-1 idiom) lifts the
-- degenerate-witness independence to a polynomial-non-root condition. The arithmetic `D(|sc|−1) − k'` flows
-- from `hKmin.1` (`def(Gc.map f) = k'`) through the shared core's ℤ-equality.
```
The `???`/design-slots of the §1.65(d) pin are now resolved: the leaf is the **`_proj`-form** (route 1), not the
full-span-form (route 2). The blueprint mints **one** new node `lem:rank-polynomial-IH-relabel-proj` (rigidity-
matrix.tex, beside the now-superseded `lem:rank-polynomial-IH-relabel`); `\uses{lem:rank-transport-relabel-of-le-finrank,
lem:extProj-preserves-rank-of-inter, lem:rank-polynomial-of-le-finrank}`.

**(f) The producer `case_I_realization_all_k` re-aimed at the coupler (the L5b-ii rewrite).** Mirror the rigid
`case_I_realization` (CaseI:2360), **not** `case_cut_edge_realization_gp`. The signature is unchanged from §1.65(e)
(all-`k`, the conditioned-pair IH, simple branch concluding the GP conjunct), but the **body** is the rigid arm's
body with the surviving-leg input swapped:
```lean
theorem case_I_realization_all_k [DecidableEq β] [Finite α] [Finite β] {n : ℕ}
    (hD : 2 ≤ Graph.bodyBarDim n) (hn : Graph.bodyBarDim n = screwDim 2)
    {k : ℤ} (G : Graph α β) (hG : G.IsMinimalKDof n k) (_hV3 : 3 ≤ V(G).ncard)
    (hSimple : G.Simple) {H : Graph α β} (hH : H.IsProperRigidSubgraph G n) {r : α} (hr : r ∈ V(H))
    (hcSimple : (G.rigidContract H r).Simple)
    (hIH : ∀ (k' : ℤ) (G' : Graph α β), G'.IsMinimalKDof n k' → V(G').Nonempty →
      V(G').ncard < V(G).ncard →
      (G'.Simple → PanelHingeFramework.HasGenericFullRankRealization 2 n G') ∧ HasPanelRealization 2 n G') :
    PanelHingeFramework.HasGenericFullRankRealization 2 n G
```
Body: H-leg rigid rank polynomial `exists_rankPolynomial_of_rigidOn_linking_set` (H is a rigid proper subgraph,
unchanged from the rigid arm); the **deficient `_proj` rank polynomial (e)** for the surviving block (replacing the
rigid `rigidContract_exterior_rank_transport` + `exists_rankPolynomial_of_rigidOn_linking_set_proj` chain); the
`G.endsOf` selector-alignment as in the rigid arm; feed all three to `hasGenericFullRankRealization_of_couple_blockTriangular_ofNormals_set`
with **`hdef` replaced by the deficient surviving target** — *here is the one signature subtlety*: the landed
coupler hard-codes `hdef : G.deficiency n = 0` (CaseI:2144) and its `hsc_proj_indep` demands the *full*
`D(|sc|−1)` (CaseI:2141), so **the coupler itself needs a deficiency-aware restate** (`..._couple_blockTriangular_ofNormals_set_kdof`,
lowering `hdef=0`→`G.deficiency n = k` and the surviving target `D(|sc|−1)`→`D(|sc|−1)−k`, the M2 conclusion to
`D(|V|−1)−k`). This is a third new decl, mechanical (the row-counting + B2-antisymmetry arithmetic of CaseI:2119
restated with `−k`). *The 6.5 sub-arm stays red → L8; `hcSimple` is the dispatch's positive-branch output.*
Statement change vs the landed `case_I_realization` → grep `blueprint/src` per the structural-edit gate.

**(g) The re-cut L5b-ii build leaves (replacing the §1.65(g) L5b-ii single leaf — exact build order, all
`buildable`).** The §1.65 decomposition had L5b-i (V6-b leaf, done as route 2) → L5b-ii (producer) → L5b-iii
(dispatch). The route correction re-cuts the *remaining* work (L5b-i's route-2 leaf is dead; the shared core and
W6e/`injOn`/U2 survive) into:

* **L5b-ii-a** — the deficient `_proj` extractor `exists_independent_panelRow_subfamily_of_le_finrank_proj` (e,
  first decl). **`P≈2`** — the rigid extractor's body (CaseI:1259) verbatim with two landed swaps (W6e for the
  un-projected source, the rigidity-free `injOn` core for the rigidity-gated one). GenericityDevice.lean or CaseI.lean
  beside the rigid sibling. The first concrete L5b-ii commit. **No blueprint node** (it is the `_proj` infra sibling,
  churn-prone — the rigid sibling has none either).
* **L5b-ii-b** — the deficient `_proj` rank polynomial `exists_rankPolynomial_of_IH_relabel_linking_set_proj` (e,
  second decl), assembling L5b-ii-a + the landed shared core + U2. **`P≈3`** (the genuinely-new assembly — the
  deficient mirror of `rigidContract_exterior_rank_transport_htransport`, the degenerate-witness → polynomial
  lift). Mints `lem:rank-polynomial-IH-relabel-proj`. **This is the V6-b leaf in its corrected (route-1) form.**
* **L5b-ii-c** — the deficiency-aware coupler restate `hasGenericFullRankRealization_of_couple_blockTriangular_ofNormals_set_kdof`
  (f, the `−k` lowering). **`P≈2`** (mechanical arithmetic restate of CaseI:2119). May fold into L5b-ii-d if small.
* **L5b-ii-d** — `case_I_realization_all_k` (f): the producer, assembling the H-leg rigid polynomial + L5b-ii-b +
  L5b-ii-c. **`P≈2`** (a clean assembly mirroring the rigid `case_I_realization` body). Mints
  `lem:case-I-realization-all-k`. Statement-grep gate before commit.
* **L5b-iii** — unchanged from §1.65(g): the `hcontract` slot-filler dispatch (`by_cases G.Simple`). **`P≈1`**
  (plumbing). Updates `lem:case-I-dispatch`; the 6.5 sub-arm stays red → L8.

**Smallest next forward commit: L5b-ii-a** (the deficient `_proj` extractor), the first leaf of the corrected
route. *Flag for the coordinator/user (no adjudication strictly required, but surfaced):* (i) the route decision is
now PINNED (route 1, not the §1.65 soft-rec route 2) — the change is grounded in the landed `case_I_realization`
mechanism, not a guess; (ii) the route-1 build adds **three new decls** (extractor + `_proj` rank polynomial +
deficient coupler) vs the route-2 fantasy's "reuse L5b-i + splice brick" — this is more Lean surface than §1.65
projected, but it is the *only* surface that produces the GP conjunct (route 2 cannot); (iii) the landed route-2
leaf `exists_rankPolynomial_of_IH_relabel_linking` is dead (delete-at-L5b-close candidate, harmless until then). No
motive / IH change either way.

**Honesty note (why this pass overrides the §1.65 soft-rec).** §1.65(c) recommended route 2 "as the smaller new
surface", explicitly soft, "pinned with the goal state open". This pass opened the goal state (the rigid
`case_I_realization` mechanism) and found route 2 structurally cannot produce the GP conjunct — the §1.64(c)/§1.65(c)
flag "do not over-commit the internal route in a pin" did its job: the route was *not* committed, the L5b-i build
followed route 2 *as a lemma* (which is sound and reused), and this pass corrects the *producer's* route before any
producer Lean was written on the wrong foundation. The L5a-i boundary-pair lesson (a wrong-for-purpose green commit
on master) is the one this avoided: had L5b-ii been dispatched on the route-2 soft-rec, it would have BLOCKED again
(as row 109 did) or — worse — produced a splice-brick assembly that cannot close.

### 1.67 The L6 signature pin — Lemma 6.8, the `k > 0` split (`hsplitPos`): the `hsplitPos` producer pins against the SETTLED §1.56(c) all-`k` IH; the eq. (6.12)–(6.17) placement reuses the landed `case_II_placement_eq612` but at a DEFICIENT `(k−1)`-dof IH, so its one rigidity-gated step (the OLD block) needs the deficiency-aware swap (`_of_rigidOn_linking` → `_of_le_finrank` at rank input `N := D(|V(Gv)|−1)−(k−1)`) — V7 RESOLVED: the W-suite (the `t=0` certify-then-rebase, `exists_shear_linearIndependent_pair`, `caseIIICandidate_exists_good_shear`) transfers WHOLESALE because it is rank-driven, not rigidity-driven, and L6 is STRICTLY SIMPLER than the `k=0` Case III (the deficient IH already supplies the full target rank `D(|V|−1)−k`, so NO Claim-6.11/6.12 redundant-row machinery, NO `h622`); no motive/IH change (2026-06-13)

> **Docs-only design pass (the L6 pin), opus.** Lean read this pass, every load-bearing decl opened
> to its `def`/`theorem` body and verified against the cited claim (clause (i) of the dispatch):
> CaseI.lean — `case_I_realization_all_k` (:9275, the all-`k` GP producer TEMPLATE this mirrors:
> manufacture `ends = G.endsOf`, IH at the smaller graph, feed the deficiency-aware coupler),
> `case_III_realization` (:7514) + `case_III_candidate_dispatch` (:7172, the `k=0` analog — its
> `h622lb` carry + `caseIIICandidate`/`caseIIICandidate_exists_good_shear` shear tail at :5346–:5390
> are the W-suite at the harder `k=0`; READ to confirm L6 needs *less*),
> `PanelHingeFramework.case_II_placement_eq612` (:3520, the eq.-(6.12)–(6.17) brick — its `hrig` +
> `exists_independent_panelRow_subfamily_of_rigidOn_linking` OLD-block at :3595, the *one*
> rigidity-gated step; everything else — NEW `e_b`-block via `exists_independent_panelRow_subfamily_of_edge`
> :3631, pin-a-body split `linearIndependent_sum_pinned_block` :3659, the `D(|V|−1)−1 = (D−1)+D(|V(Gv)|−1)`
> count arithmetic :3683–:3697 — is rigidity-agnostic);
> GenericityDevice.lean — `BodyHingeFramework.exists_independent_panelRow_subfamily_of_le_finrank`
> (:718, W6e, the rank-input extractor the deficient OLD block swaps in — `hN : N ≤ finrank (span
> rigidityRows)`, NO rigidity) and `…_of_rigidOn_linking` (:788, just the `N := D(|V|−1)` corollary of
> it via `finrank_span_rigidityRows_of_rigidOn`); PanelLayer.lean —
> `setOf_not_shear_linearIndependent_subsingleton` (:714, the bad-shear-set bound, uses ONLY
> `hgab : LinearIndependent ![n_a, n_b]`, dof-agnostic) + `exists_shear_linearIndependent_pair` (:773);
> ForestSurgery.lean — `splitOff_isMinimalKDof_of_pos` (:3472, KT Lemma 4.8: `G.splitOff v a b e₀` is
> minimal `(k−1)`-dof given `0 < k` + no proper rigid subgraph — the dof-DECREMENT engine, distinct
> from the landed 0-dof `splitOff_isMinimalKDof`), `splitOff_removeVertex_minimalKDof` (:3198);
> ReducibleVertex.lean — `exists_degree_eq_two` (:673, KT Lemma 4.6, the degree-2 vertex);
> PanelHinge.lean — `HasGenericFullRankRealization` (M3, :1035 — GP + ℤ-rank + link-recording +
> `AlgebraicIndependent ℚ`, the L6 conclusion). KT 2011 §6.3 read end-to-end against the PDF this pass
> (pp. 677–679): Lemma 6.7 (`G_v^{ab}` simple), Lemma 6.8 + its full proof (eqs. (6.11)–(6.17), the
> column ops, the Lemma-5.2 nonparallel conversion), and p. 680's explicit `k=0`-vs-`k>0` contrast
> ("we only have `rank ≥ 5 + 6(|V∖v|−1) = 6(|V|−1)−1` in the current [`k=0`] situation, which does not
> complete the proof" — i.e. the `h622`/redundant-row machinery exists *only* because `k=0`). No
> `.lean`/`.tex` edits this pass; the L2 `hsplitPos` slot (§1.59(a)) is the producer's contract.

**The slot the L6 producer fills.** L2's `hsplitPos` slot (`minimal_kdof_reduction_all_k`, §1.59(a)),
at `P G = Pc G := (G.Simple → HasGenericFullRankRealization 2 n G) ∧ HasPanelRealization 2 n G`
(§1.56(b) M4):

```lean
(hsplitPos : ∀ (k : ℤ) (G : Graph α β), G.IsMinimalKDof n k → 0 < k →
  3 ≤ V(G).ncard → G.TwoEdgeConnected →
  (∀ H : Graph α β, ¬ H.IsProperRigidSubgraph G n) →
  (∀ (k' : ℤ) (G' : Graph α β), G'.IsMinimalKDof n k' → V(G').Nonempty →
    V(G').ncard < V(G).ncard → P G') → P G)
```

L6 discharges this exactly as L5 discharged `hcontract` (§1.56(c)/(d)): the bare conjunct is **free**
(G0 `simple_of_isMinimalKDof_of_noRigid` gives `G.Simple` from `hnp`, so the GP conjunct's hypothesis
`G.Simple` always fires, and `HasPanelRealization` is M4-forgetful of `HasGenericFullRankRealization`
— `hasPanelRealization_of_generic`). So the *content* is the **GP conjunct producer**: a
`HasGenericFullRankRealization 2 n G` builder under the slot's hypotheses + the all-`k` IH. This
mirrors `case_I_realization_all_k`'s structure (§1.66(g) L5b-ii-d) at a *splitting* reduction instead
of a *contraction*.

**(a) The pinned L6 producer.** CaseI.lean, beside `case_III_realization` (the `k=0` sibling; L6 is
the `k>0` sibling, sharing the eq.-(6.12) placement). One GP producer:

```lean
/-- **Lemma 6.8, the `k > 0` split** (`lem:case-II-realization` at `k > 0`; `hsplitPos` carry,
Phase 22i L6). Katoh–Tanigawa 2011 §6.3, p. 677. A 2-edge-connected minimal `k`-dof-graph
(`k > 0`, `|V| ≥ 3`) with no proper rigid subgraph carries a generic full-rank realization. -/
theorem PanelHingeFramework.case_II_realization_all_k [DecidableEq β] [Finite α] [Finite β]
    {n : ℕ} (hD : 6 ≤ Graph.bodyBarDim n) (hn : Graph.bodyBarDim n = screwDim 2)
    (hfresh : ∀ G' : Graph α β, ∃ e₀ : β, e₀ ∉ E(G'))
    {k : ℤ} (G : Graph α β) (hG : G.IsMinimalKDof n k) (hk : 0 < k) (hV3 : 3 ≤ V(G).ncard)
    (htec : G.TwoEdgeConnected)
    (hnoRigid : ∀ H : Graph α β, ¬ H.IsProperRigidSubgraph G n)
    (hIH : ∀ (k' : ℤ) (G' : Graph α β), G'.IsMinimalKDof n k' → V(G').Nonempty →
      V(G').ncard < V(G).ncard →
      (G'.Simple → PanelHingeFramework.HasGenericFullRankRealization 2 n G') ∧
        HasPanelRealization 2 n G') :
    PanelHingeFramework.HasGenericFullRankRealization 2 n G
```

Design notes:

* **`hD : 6 ≤ bodyBarDim n` + `hn : bodyBarDim n = screwDim 2`** match `case_I_realization_all_k`
  (:9276) and `case_III_realization` (:7515 has `hD`; the `hn` B2 input is the L5b-ii-c addition).
  `hfresh` supplies the fresh split-off edge `e₀ ∉ E(G)` (as `case_III_realization` carries it for
  the splitting case; `case_I_realization_all_k` does not need it because contraction adds no edge).
  `k : ℤ` comes from the L2 `hsplitPos` binder; the four typeclasses are the slot context.
* **`hsplitPos` slot → producer hypotheses.** The slot supplies `hG`, `0 < k` (`hk`), `3 ≤ ncard`
  (`hV3`), `htec`, `hnoRigid`, and the all-`k` IH. The producer adds `hD`/`hn`/`hfresh` (ambient data
  it carries itself, as `theorem_55_d3` already does — the principle has none, §1.59(b) audit row
  `hsplitPos`). `htec` is **not consumed** by the rank argument (KT uses 2EC only to get Lemma 6.7's
  simplicity of `G_v^{ab}` — which the producer re-derives from `hnoRigid` directly via the
  triangle-forces-rigid-subgraph argument, KT Lemma 6.7(ii)); it is carried to match the slot and is
  ignorable, exactly the §1.59(b) note.
* **The bare conjunct is free (the `hsplit`-style discharge).** This producer concludes
  `HasGenericFullRankRealization` (the GP conjunct) directly; the slot's *pair* is closed at L9 by
  G0 (`simple_of_isMinimalKDof_of_noRigid hG hnoRigid` gives `G.Simple`, firing the conditioned GP
  arm) ∘ M4 forgetful (`hasPanelRealization_of_generic`). L6 itself need only build the GP conjunct.

**(b) The construction (KT eqs. (6.11)–(6.17), all reuse verified against the landed Lean).**

1. **Degree-2 vertex + dof-decrement split (graph side).** `exists_degree_eq_two`
   (ReducibleVertex:673, KT 4.6) under `htec`/`hnoRigid`/`hV3` gives `v` of degree 2 with
   `N_G(v) = {a, b}`; `splitOff_isMinimalKDof_of_pos` (ForestSurgery:3472, KT 4.8) under `hk`/`hnoRigid`
   gives `G_v^{ab} := G.splitOff v a b e₀` minimal `(k−1)`-dof. `G_v^{ab}` is **simple** by KT 6.7(ii)
   (no proper rigid subgraph rules out the `ab` parallel edge; the landed `Graph.splitOff` simplicity
   facts + `hnoRigid` discharge it — confirm the exact lemma at the build, V7-residual (b1), expected
   the same `loopless_of_isMinimalKDof`/`splitOff` simplicity facts the 0-dof Case-III uses).
2. **IH at the deficient split-off.** The all-`k` IH at `k' = k−1`, `G' = G_v^{ab}` (nonempty —
   contains `a`; smaller — `|V∖v| = |V|−1`) gives the conditioned pair; its `.1` (at `G_v^{ab}` simple)
   gives `HasGenericFullRankRealization 2 n (G_v^{ab})` — a generic realization `(G_v^{ab}, q)` at
   ℤ-rank `D(|V∖v|−1) − (k−1)` (eq. 6.11). This is the **deficient** IH (rank `< D(|V∖v|−1)` for
   `k > 1`), the single substantive departure from the `k=0` Case III where the IH is rigid.
   Transversality of the IH `ab`-hinge — `hgab : LinearIndependent ![q(a,·), q(b,·)]` — comes from
   the IH realization's general position (`IsGeneralPosition` at the distinct `a ≠ b ∈ V(G_v^{ab})`),
   exactly as `case_III_candidate_dispatch` extracts it.
3. **The eq. (6.12) placement — `case_II_placement_eq612` AT A DEFICIENT IH (the one reuse delta).**
   The landed `case_II_placement_eq612` (CaseI:3520) is the eq.-(6.12)–(6.17) brick: it places `v`'s
   normal at `n_a + t·n_b` (`t ≠ 0`), reproduces the `vb`-row as the `ab`-row (shear identity
   `panelSupportExtensor_add_smul_right`), keeps the `va`-hinge a nondegenerate line `L ⊂ Π(a)`, and
   the block-triangular column ops (eq. 6.16) give the rigidity-row family. **Its OLD block is the
   *only* rigidity-dependent step**: it consumes `hrig : ...IsInfinitesimallyRigidOn V(Gv)` ONLY to
   feed `exists_independent_panelRow_subfamily_of_rigidOn_linking` (:3595), producing `D(|V(Gv)|−1)`
   rows. At `k > 0` the IH is deficient, so L6 needs a **deficiency-aware variant**
   `case_II_placement_eq612_kdof` (CaseI.lean, beside the rigid one) — `case_II_placement_eq612`'s body
   *verbatim* with two swaps (the V7 delta, exactly the L4b-1→L5b-ii-a precedent):
   - (i) replace `hrig` + `_of_rigidOn_linking` with the rank input `hNrank :
     screwDim k * (V(Gv).ncard − 1) − (k−1) ≤ finrank (span (ofNormals Gv ends q).rigidityRows)` fed
     to the deficiency-aware `exists_independent_panelRow_subfamily_of_le_finrank` (W6e, :718, NO
     rigidity), giving `D(|V(Gv)|−1) − (k−1)` OLD rows;
   - (ii) shift the count arithmetic (:3683–:3697) from `D(|V(G)|−1)−1 = (D−1)+D(|V(Gv)|−1)` to
     `D(|V(G)|−1)−k = (D−1)+[D(|V(Gv)|−1)−(k−1)]` (the same `Nat.mul_succ` identity, lowered by `k−1`).
   Everything else — the NEW `e_b`-block, the pin-a-body split, the `hane`/`hnewne` transversality —
   is rigidity-agnostic and copies unchanged. The deficient rank input `hNrank` is the IH's ℤ-rank
   eq. (6.11) (`HasGenericFullRankRealization`'s rank conjunct at `G_v^{ab}`), transported to the
   shared seed `q₀` exactly as the rigid brick transports `hrig` (the `withNormal`/`infinitesimalMotions_eq`
   override of the unhinged `v`, :3561–3590, is rigidity-free — it transports a *motion space* and
   hence any rank, not just rigidity).
4. **The Lemma-5.2 nonparallel conversion → the GP conjunct (V7, the W-suite at `k > 0`).** The
   eq.-(6.12) placement gives `rank R(G,p₁) ≥ D(|V|−1) − k` at the *parallel* candidate (panels `Π(v)`,
   `Π(a)` parallel). KT converts to nonparallel by Lemma 5.2 "without decreasing the rank"; the project
   does this by the **certify-then-rebase W-suite the `k=0` Case III already uses** (`case_III_candidate_dispatch`
   :5346–5390), which is **rank-driven, not rigidity-driven**, so it transfers WHOLESALE:
   `exists_independent_panelRow_subfamily_of_le_finrank` re-extracts a literal `t=0` family of the
   certified rank; `setOf_not_shear_linearIndependent_subsingleton` (PanelLayer:714, uses ONLY `hgab`)
   bounds the bad-shear set; `caseIIICandidate_exists_good_shear` (CaseI:4639) picks a `t* ≠ 0` outside
   it; the sheared seed `q₀ : v ↦ n_a + t*·n_b` realizes `(G, p₁)` nonparallel at the same rank.
   The general-position + `AlgebraicIndependent ℚ` conjuncts of M3 come from the same fresh-shared-seed
   genericity device the rigid producers use (the seed is alg-indep + general-position by construction;
   the rank polynomial's non-root supplies both). **V7 verdict: substantial reuse confirmed (KT built
   the W-suite for the *harder* `k=0` case; the `k>0` case is a strict sub-problem of it).**

**(c) Why L6 is STRICTLY SIMPLER than the `k=0` Case III (the V7 crux, machine-checked against KT
p. 680).** At `k = 0` the IH `(G_v^{ab}, q)` is rigid (`rank = D(|V∖v|−1)`), so eq. (6.12) gives only
`(D−1) + D(|V∖v|−1) = D(|V|−1) − 1` — **one row short** of the `k=0` target `D(|V|−1)`. Closing that
gap is the entire Claim-6.11/6.12 redundant-`ab`-row machinery (the largest proof in KT) and is what
`case_III_candidate_dispatch` carries as `h622lb`. At `k > 0` the IH is deficient (`rank =
D(|V∖v|−1) − (k−1)`), so eq. (6.12) gives `(D−1) + [D(|V∖v|−1) − (k−1)] = D(|V|−1) − k` — **exactly the
target**, no row short. KT states this verbatim (p. 680): for `k = 0` "we only have `rank ≥ 5 +
6(|V∖v|−1) = 6(|V|−1) − 1` … which does not complete the proof", whereas Lemma 6.8 "[obtains] the
desired rank". So **L6 reuses NONE of the Case-III crux**: no `h622`, no `caseIIICandidate` candidate
dispatch over `D` candidates, no redundant-row extraction. It uses only the eq.-(6.12) placement (at
the deficient IH) + the single-candidate shear conversion. This is why §1.56(d) called it "NEW
assembly, mostly landed parts" and the prompt called it the tractable `k > 0` arm.

**(d) Verification items.** **V7 RESOLVED** (this pass): the W-suite transfers wholesale (it is
rank-driven); the one delta is the deficiency-aware `case_II_placement_eq612_kdof` swap (V6-b /
L5b-ii-a precedent, near-mechanical). **No motive/IH change, no user adjudication needed** — clause
(ii) of the dispatch: the pin is honest and buildable from landed parts. Two **residual build-time
verification items** (not blockers, not motive-level — settle at the leaf's design recon, the
project's standing per-layer discipline): **(b1)** the exact landed lemma for "`G_v^{ab}` simple from
`hnoRigid`" (KT 6.7(ii)) — expected the `splitOff`-simplicity + `loopless_of_isMinimalKDof` facts the
0-dof dispatch already uses; **(b2)** whether `case_II_placement_eq612`'s `Gv` parameter (abstract
`Gv ≤ G`, `v ∉ V(Gv)`) is fed `G_v^{ab} = G.splitOff v a b e₀` (which contains the `ab` edge so `hgab`
is realized) vs `G.removeVertex v` — KT's `(G_v^{ab}, q)` is the split-off (eq. 6.17's `ab`-row), and
the brick reproduces `q(ab)` via `panelSupportExtensor_add_smul_right`, so `Gv = splitOff`; confirm
the `removeVertex`-vs-`splitOff` selector wiring at the build (the rigid dispatch threads both via
`hle : Gv.IsLink → Gab.IsLink`, :7235).

**(e) The L6 slice cut (build order, all `buildable`).** Mirrors the L5b-ii cut (§1.66(g)): the
deficiency-aware placement brick first, then the producer.

* **L6a** — `PanelHingeFramework.case_II_placement_eq612_kdof` (CaseI.lean, beside
  `case_II_placement_eq612`): the deficient eq.-(6.12)–(6.17) brick. **`P≈2`** — the rigid brick's body
  verbatim with the two (b)(3) swaps (W6e for the OLD block, `k−1`-lowered count). The first concrete
  L6 commit. **No blueprint node** (it is the `_kdof` infra sibling of `case_II_placement_eq612`, which
  itself mints `lem:case-II-realization-placement` — restate-or-leave the rigid node, decide at build;
  the `_kdof` variant is churn-prone infra like the L5b-ii-a `_proj` extractor, so default no node).
* **L6b** — `PanelHingeFramework.case_II_realization_all_k` (the (a) producer), assembling: the
  degree-2 split (b1), the deficient IH (b2), `case_II_placement_eq612_kdof` (L6a), and the W-suite
  shear conversion (b4). **`P≈3`** (the genuinely-new assembly — the deficient placement + shear tail,
  the L6 analog of `case_III_realization`'s body but *without* the candidate dispatch). Mints
  `lem:case-II-realization` (restating it green at the `k > 0` content; the node currently red — its
  `k=0` half is Case III / L7). Statement-grep gate before commit (the `\lean{...}` survives a content
  flip; grep `blueprint/src` per `CLAUDE.md` *Structural-edit phases*).

**Estimate: ~2–3 commits.** L6a is near-mechanical; L6b is the assembly. The 6.5 sub-arm does NOT
enter L6 (it is the `hcontract`/Case-I arm, carried as `h65` → L8); L6 is purely the `hsplitPos`
splitting case. *Buildable, no motive/IH change.*

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
