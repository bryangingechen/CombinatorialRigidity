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

## 2. Shared-infra map (green vs. missing across the layer)

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
