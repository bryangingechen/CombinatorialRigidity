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

### 1.25 Phase 22c opens — Case III at `d=3` (KT Lemma 6.10): the layer design recon, first pass (2026-06-05)

22b closed (Claim 6.4 discharged; `lem:case-I-realization` fully green). **Phase 22c opens on Case III
at `d=3` / Track B** — KT §6.4.1, Lemma 6.10, the `theorem_55.hsplit` branch at `k=0`, the
conjecture's crux (the single largest proof in KT, ~12 pages). Per `DESIGN.md` *Scale-up: design the
LAYER, not just the node* and the user's design-pass-first instruction, 22c opens with a **layer-level
design recon, not a build** — Case I burned ~10 node-by-node commits before a layer pass surfaced the
binding gap; Case III is more interlocking (three candidate frameworks sharing one candidate
structure + Claim 6.11 wiring the row matroid to `M(G̃_v^{ab})` + Claim 6.12's extensor-span
genericity), so the layer recon runs first. This is the **first recon pass** (docs-only, no Lean /
`\leanok` / blueprint): read the whole Lemma-6.10 argument against the primary source + the green
infra it bottoms on; the per-piece needs/supplies map + the open recon questions are recorded in
`notes/Phase22c.md` (its *First design-recon pass* + *open recon questions*), the canonical 22c log.

**Verified against the KT 2011 primary source (pdf pp. 34–45).** Lemma 6.10: `G` 2-edge-connected
minimal 0-dof, `|V| ≥ 3`, no proper rigid subgraph, (6.1) holds ⟹ a *nonparallel* panel-hinge
realization in 3-space at `rank R(G,p) = 6(|V|−1)` (`D = 6` at `d=3`). The one-row shortfall: a single
eq. (6.12) degenerate placement `p₁` (`p₁(vb) = q(ab)`, the `vb`-row reproducing the `e₀=ab`-row) is
block-triangular with `R(G_v^{ab},q)`, giving `rank ≥ (D−1) + D(|V∖{v}|−1) = D(|V|−1) − 1` — one
short (KT printed p. 680). The `D`-candidate argument supplies the missing row: KT build three
candidates `(G,p₁),(G,p₂),(G,p₃)` (pdf p. 37) and show one is full rank, via Claim 6.11 (the
redundant `(ab)i*`-row, eq. 6.23 `rank R(G_v^{ab}∖(ab)i*,q) = rank R(G_v^{ab},q) = 6(|V∖{v}|−1)`, off
Lemma 4.3(ii) + the IH — the combinatorial↔linear bridge to `M(G̃_v^{ab})`) and Claim 6.12 (if all
candidates fail, a nonzero `r ∈ ℝ⁶ ⟂` all extensors on `d+1` generic panels, which by the green
Phase-17 **Lemma 2.1** span `ℝ⁶` — contradiction; the degree-2 condition forces all candidates to
test the *same* `r`, eq. 6.44). General-`d` (Lemma 6.13, pdf p. 46) stays Phase 23.

**Scope cut settled** (`notes/Phase22c.md` *Sub-phase scope cut*): 22c = Case III at `d=3` (the crux);
the `d=3` assembly (`prop:rigidity-matrix-prop11` `hub` + `thm:theorem-55` flip + the
`case_I_realization`→`theorem_55_generic` Case-I wiring) is the **likely 22d, deferred** until 22c's
shape is clear (same defer-the-finer-cut discipline as 22a→22b+, 22b→22c+). **Next concrete commit:**
continue the recon (still docs-only) — settle the four open recon questions (candidate normal form vs.
three inlined copies; `d=3`-first; Claim 6.11's row-matroid bridge shape; Claim 6.12's "same `r`"
packaging) — *before* cutting the first Lean node. No exposition-ledger entry yet: the captured Case-III
ledger lines (`lem:case-II-realization`/eq. 6.12; Case III at large) already exist (`notes/BlueprintExposition.md`),
status stays `pending` (write at 22c close, once `sorry`-free).

### 1.26 Phase 22c recon, second pass — the candidate structure, the four open questions resolved, and the FIRST-CHUNK scope cut (2026-06-05)

Second (still docs-only, decision-support) recon pass, **re-read against the primary source**
(KT 2011 §6.4.1, pdf pp. 34–37 [candidate construction + sketch], pp. 44–45 [Claims 6.11/6.12
rigorous]). It (a) pins the shared candidate structure, (b) answers the four open recon questions
from §1.25 / `notes/Phase22c.md`, and (c) — folding in the user's fresh direction that Case III at
`d=3` *and* the `d=3` assembly may each need multiple phases — **re-cuts 22c's scope to the first
tractable chunk**, not all of `lem:case-II-realization` + `lem:case-III`.

**The shared candidate structure (verified, KT pp. 34–37).** No proper rigid subgraph + `d=3` ⟹
(Lemma 4.6) two *adjacent* degree-2 vertices `v, a`, with `N_G(v) = {a,b}`, `N_G(a) = {v,c}`. Both
`G_v^{ab}` and `G_a^{vc}` are minimal 0-dof (Lemma 4.8), and `G_a^{vc} ≅ G_v^{ab}` (the panel of `a`
in `(G_v^{ab},q)` plays the role of the panel of `v` in `(G_a^{vc},q_ρ)`, Fig. 6(b)(f)(g)). The IH
(6.1) supplies one generic nonparallel realization `(G_v^{ab}, q)` with `rank R = 6(|V∖{v}|−1)` (eq.
6.18). **All three candidates share this one `q`**: `(G,p₁)`/`(G,p₂)` are built on `(G_v^{ab},q)`
(eqs. (6.12)/(6.19), differing only in which of `va`/`vb` carries the degenerate `q(ab)` placement),
`(G,p₃)` on `(G_a^{vc},q_ρ)` (eqs. (6.31)/(6.32)), where `q_ρ` is `q` transported across the iso. So
the *shared data* parametrizing a candidate is `(q, the degenerate hinge choice, the free panel line
L ⊂ Π(·))`; the three differ only in which panel (`Π(a)`, `Π(b)`, `Π(c)`) the free line lives on.

**Open question 1 — candidate normal form: ABSTRACT a single candidate lemma, instantiate ×3.**
The three candidates are *not* three independent constructions: `p₁`/`p₂` are literally symmetric
(`a ↔ b`, KT eq. (6.19) "symmetric to Claim 6.9"), and `p₃` is `p₁` precomposed with the iso `ρ`.
Their row-ops are *identical* (KT performs them once for `p₁`, then says "the same analysis" for
`p₂`/`p₃`, p. 35). So the formalization should state the per-candidate row-op + `+(D−1)` argument
**once**, parametrized by `(degenerate hinge, free panel)`, and instantiate three times — KT's own
structure. The Claim-6.12 contradiction then quantifies over the three instances' residual normals
`r, r', r''` and uses the eq. (6.44) forcing (below) to identify them.

**Open question 2 — `d=3`-first: YES, build the `D=6`/3-candidate case concretely first.** KT itself
does §6.4.1 (`d=3`, three candidates) then §6.4.2 (general `d`, Lemma 6.13, a length-`d` chain); the
project follows that cut (general `d` stays Phase 23). The "candidate normal form" of question 1 is
the right *internal* abstraction even within `d=3` (it is what Lemma 6.13 later re-instantiates along
the chain), but the candidate *count* and the `(4 choose 2)=6` extensor span are concretely `d=3`.

**Open question 3 — Claim 6.11's row-matroid bridge: it routes through KT Lemma 4.3(ii) + the IH,
landing as a *redundant-row existence* fact `R(G_v^{ab}, q; (ab)i*, ·)` is a row-combination of the
others.** KT's redundant row comes from: in `M(G̃_v^{ab})`, at least one `ãb` fiber edge is *not* in a
base (Lemma 4.3(ii) — there are `D=6` parallel `ãb` copies but a base uses at most `D−1` of any single
fiber when… [the IH `def`-count]); the IH then converts that combinatorial non-base edge to a linear
row-dependency (eq. 6.24 / 6.43). The Lean bridge is the green Phase-19 `M(G̃)` ↔ row-independence
machinery (`matroidMG_indep_iff`, the `def = corank` bridge `thm:def-eq-corank`), but the *conversion*
"combinatorial non-base edge ⟹ a redundant rigidity row at the IH realization" is genuinely new analytic
content — it is the IH applied at the rigidity matrix, the hardest non-extensor step (KT calls it out
on p. 680). This is the **D-candidate crux**, not the first chunk.

**Open question 4 — Claim 6.12's "same `r`": it is eq. (6.44), and it FOLDS into the candidate normal
form's contradiction step, NOT a separate brick.** The forcing is: `r := Σ_j λ_(ab)j r_j(q(ab))` is the
residual normal of `M₁`/`M₂`; for `M₃` the residual is `Σ_j λ_(ac)j r_j(q(ac))`, and eq. (6.44) shows
`r = −Σ_j λ_(ac)j r_j(q(ac))` **because `a` is degree-2 in `G_v^{ab}`** (only `ab, ac` incident to `a`,
so the `a`-block of the row-dependency (6.43) has exactly two terms). So all three candidates'
singularity puts the *same* `r` in the orthogonal complement of the extensors on `Π(a)`/`Π(b)`/`Π(c)`
respectively; Claim 6.12 then takes four affinely-independent points `p₁ = Π(a)∩Π(b)∩Π(c)`, `p₂ ∈
Π(a)∩Π(b)∖Π(c)`, etc., and **Lemma 2.1** (`omitTwoExtensor_linearIndependent`, green, the `(4 choose
2)=6` 2-extensors of 4 aff.-indep. points span `ℝ⁶`) contradicts `r ≠ 0`. The extensor half maps onto
Phase-17's Lemma 2.1 *directly*; the residual-normal bookkeeping (eq. 6.44, the degree-2 forcing) is
the candidate-normal-form's shared `r`, so it does not need its own node — it is the glue between the
three candidate instances and the Lemma-2.1 application.

**The first-tractable-chunk cut (the load-bearing scope decision, folding in the user's direction).**
The recon partitions Lemma 6.10 into three strata of difficulty:
1. **The eq. (6.12) `+(D−1)` block-triangular placement** — `buildable`. `p₁(va) = L ⊂ Π(a)`,
   `p₁(vb) = q(ab)` reproduces the `e₀ = ab` row; column ops (KT eq. (6.16)) make `R(G,p₁)`
   block-triangular with `R(G_v^{ab},q)` a submatrix ⟹ `rank ≥ 5 + 6(|V∖{v}|−1) = D(|V|−1)−1`. This is
   the *direct* reuse of the green Phase-21b row infra (N7b-0/1/2/3 + `linearIndependent_sum_pinned_block`),
   the same machinery the eq. (6.12) warm-up in §3 Track B already names. **This is the first chunk** —
   it is the largest self-contained, green-infra-fed piece, and it produces the candidate scaffold the
   crux then completes.
2. **Claim 6.11 (the redundant `(ab)i*`-row)** — `research-shaped`, the **D-candidate crux**. The
   combinatorial↔linear conversion (Lemma 4.3(ii) ⟹ a redundant rigidity row at the IH realization).
   The single highest-risk node in Phases 22–23 (`notes/Phase22-realization-design.md` §4).
3. **Claim 6.12 (the extensor-span contradiction) + the candidate normal form + eq. (6.44)** — the
   assembly that turns "each candidate singular ⟹ `r ⟂` its panel extensors" + "same `r`" + Lemma 2.1
   into "some candidate is full rank". Bottoms on the green Lemma 2.1, but needs all three candidates'
   residual-normal data, so it composes *after* strata 1 and 2.

**Decision: 22c = stratum 1 (the eq. (6.12) `+(D−1)` placement) as the first sub-phase, with the
candidate-framework scaffold it sets up.** Strata 2–3 (the redundant-row crux + the candidate-normal-form
/ Claim-6.12 assembly) are **likely their own later sub-phase(s)** — name the *next* distinct sub-phase
when stratum 1's shape is clear, do NOT pre-commit its internal node list now (the same defer-the-finer-cut
discipline as 22a→22b+, 22b→22c+, and 22c→22d). 22c does **not** claim to land all of
`lem:case-II-realization` + `lem:case-III` in one phase. This matches both the user's explicit direction
("let's not try to cram too much into 22c") and the design-pass-first mandate: stratum 1 is the buildable
warm-up that exercises the placement + row infra on the `k=0` target and exposes the candidate structure,
*before* the genuinely-research-shaped crux is scheduled.

**Why this is the right first cut and not, e.g., the crux first.** The crux (stratum 2) is research-shaped
and its math-first decomposition is the natural target for a *dedicated* sub-phase (it is ~half of KT's
~12-page proof and the single highest-risk node). Stratum 1 is `buildable` from green infra and is a
*prerequisite scaffold* for strata 2–3 (the candidate frameworks, on which the residual-normal `r` and the
missing row are defined, are exactly the eq. (6.12)/(6.19)/(6.32) placements). Building the scaffold first
de-risks the crux's recon (it makes the candidate structure concrete in Lean) and gives a green, useful
`+(D−1)` lower-bound brick even before the crux lands. This is the same staging as Track A's "N6a first,
then the simple-case crux" and Track B's own "eq. (6.12) placement is the buildable warm-up; Lemma 6.10 is
the crux and the natural decompose-math-first target for a dedicated sub-session" (§3 Track B build order).

**Next concrete commit (post-this-recon).** With the four questions settled and the first-chunk cut made,
the next commit is the *first Lean node* of stratum 1 — the eq. (6.12) degenerate placement producing the
`+(D−1)` block-triangular lower bound, cut leaf-most-first against the green N7b-0/1/2/3 +
`linearIndependent_sum_pinned_block` infra. Re-recon stratum 1's node order at that build's open (it is
`buildable`, so a math-first decomposition is light, but confirm the count `5 + 6(|V∖{v}|−1) = D(|V|−1)−1`
closes from the named green inputs before scheduling — the honesty gate's second half). The crux (strata
2–3) gets its math-first decomposition when its sub-phase opens.

### 1.27 Phase 22c, third pass — reconcile the blueprint Case-II nodes to the eq. (6.12) row-side route, before any Lean build (2026-06-05)

Third docs-only commit (still decision-support; no Lean / `\leanok` / blueprint-`\lean{…}` flips). The
user paused before the stratum-1 build to do **heavy up-front design**, and a review found a concrete
build-blocker: the **live blueprint prose for the exact nodes 22c builds** still described two superseded
dead-ends, while the corrected understanding (eq. (6.12) degenerate placement) lived only in the notes
(`notes/Phase21b.md` *Finding A*, §1.25–§1.26 above). A node-by-node build against that prose would have
re-derived the wrong route. This commit reconciles the blueprint and records the build-ready node cut.

**The divergence (verified against the files).** Two nodes, each self-inconsistent (statement said one
thing, proof did another):
- `lem:case-II-realization` (`case-ii.tex`): statement said the motion-side M3
  (`lem:case-II-placement-motion-side-assembly`) "was NOT KT's argument … superseded," yet its **proof
  still routed through M3** (re-insert `v`, pin via M2, conclude rigid-on-`V(G)`).
- `lem:case-II-realization-placement` (`genericity-and-count.tex`): its body described an
  N7b-0/1/2/3/4 plan with N7b-4 (`lem:case-II-placement-e0-recovery`) marked superseded/"geometrically
  unbuildable" and re-routed to motion-side M3, yet its **proof still consumed N7b-4** (the
  `$e_0$-free old block`), and the "rank-lift, motion-side" subsection still called the motion-side route
  "The corrected … genuine geometric heart" and claimed it "supersedes" the row-side placement node.

**The corrected route (KT §6.3 Lemma 6.8 / eq. (6.12), the canonical record).** The live placement is the
**row-side degenerate placement**: `p₁` agrees with the IH `q` on `G−v`, `p₁(va)=L⊂Π_q(a)` a `(d−2)`-hinge,
and `p₁(vb)=q(ab)` placing `v`'s `b`-hinge at the very `e₀=ab` hinge of `q` so the `vb`-row **reproduces**
the `e₀`-row of `R(G_v^{ab},q)`. Column ops (KT eq. (6.16)) make `R(G,p₁)` block-triangular with
`R(G_v^{ab},q)` a submatrix ⟹ `rank ≥ (D−1) + D(|V∖{v}|−1) = D(|V|−1)−1`. The `e₀`-recovery the row-side
recons sought (N7b-4) is real but is *not* an `e₀`-free block (none exists — `G−v` is not rigid); it is
the reproduced `vb`-row. The motion-side M1/M2/M3 is *not* KT's argument: M3 assumes a `G''`-motion is
constant on `V(G)∖{v}`, which the non-rigid `G−v` does not force (only `G_v^{ab}`, which has `e₀`, does).

**What this commit edited (blueprint).** `lem:case-II-realization`: re-pointed statement+proof `\uses` from
M3 to `lem:case-II-realization-placement`; proof now routes through the eq. (6.12) placement + N7a closure.
`lem:case-II-realization-placement`: statement body + the enumerate decomposition + proof rewritten to the
eq. (6.12) route (the per-row match `hrow` of N7b-2's transport IS the `p₁(vb)=q(ab)` reproduction; N7b-4
dropped from the live `\uses`); the "rank-lift, motion-side" subsection relabelled an *audit-trail* of two
superseded dead-ends. **Retain-with-marker** (the conservative choice flagged in the task as a deliberate
design decision — delete-vs-retain has audit-trail value and the green sub-nodes N7b-0/1/2/3 still need to
sit beside their history): N7b-4 (`lem:case-II-placement-e0-recovery`), M3
(`lem:case-II-placement-motion-side-assembly`), and the helpers M1
(`lem:case-II-placement-disjoint-line-meet`), M2 (`lem:case-II-placement-pin-vertex`) are **kept, struck,
with explicit "superseded — not on the live route" markers**; no live node `\uses` them (M3 is now an
orphan-off-the-live-route, correct). The green N7b-0/1/2/3 sub-nodes stay green (reused by Case I and by
this route). All four target/Case nodes (`lem:case-II-realization`, `lem:case-III`) **stay red** — 22c
lands the eq. (6.12) `+(D−1)` brick toward them.

**Reuse from Phase 22b — the de-risking question, answered.** The eq. (6.12) "place the `vb`-hinge at
`q(ab)` to reproduce a row" is the *same* degenerate-placement-reproduces-a-row *idea* as 22b's U1/U2, but
22b's concrete machinery is **not** reused for stratum 1, for a structural reason: 22b's
`degeneratePlacement r t nrm = nrm ∘ collapseTo r t`, `extProj t`, and
`panelRow_collapseTo_comp_extProj_dualMap` implement a **block collapse** of an entire rigid block `V(H)→r`
(Case I's contraction `Gc.map (collapseTo r V(H))`), with an exterior-column projection peeling off the
collapsed block. Stratum 1's `p₁(vb)=q(ab)` is a **single-vertex** placement reproducing **one** row, with
**no** block collapse and **no** exterior projection — the block-triangularity comes from the pin-a-body
column split, not from projecting away a rigid block. So stratum 1 reuses the **green N7b row infra**
near-wholesale (N7b-0 `exists_independent_panelRow_subfamily_of_rigidOn`, N7b-1
`exists_independent_panelRow_subfamily_of_edge`, N7b-2 `exists_independent_panelRow_transport`, N7b-3
`linearIndependent_sum_pinned_block` in `RigidityMatrix.lean`, N7a
`hasFullRankRealization_of_independent_panelRow`) — *these were built in Phase 21b for exactly this
`1`-extension placement*. The **one genuinely-new Lean brick** is the placement `p₁` + the per-row
reproduction `hrow` (the `vb`-row = `e₀`-row equality) that N7b-2's transport consumes. (If a future need
for a block-collapse arises in strata 2–3, *then* 22b's `extProj` machinery is the reuse target — not now.)

**Honesty gate (2nd + 3rd halves) on the stratum-1 cut.** *2nd (count):* `(D−1) + D(|V∖{v}|−1) =
D(|V|−1)−1 = 6|V|−7` at `D=6`, closing from N7b-1 (`D−1`) + N7b-0 (`D(|V|−2)`, full because the `k=0` IH is
full rank on `V(G_v^{ab})` by KT Lemma 4.8(i)). One short of `D(|V|−1)` — the Case-III missing row, strata
2–3. *3rd (structural fidelity):* KT eq. (6.16)'s **block-triangular column ops** are reproduced by
`linearIndependent_sum_pinned_block` (pin-a-body: new rows in `v`'s screw column, old rows off it), and the
eq. (6.12) `p₁(vb)=q(ab)` **row reproduction** is the per-row `hrow` of the N7b-2 transport — KT's argument
*structure*, not a re-expression. This is the check Case I failed (a motion-space splice glue silently
replaced KT's block-triangular structure, accreting bridge hypotheses; `DESIGN.md` *Match the source's
argument structure*); stratum 1 passes it because the project's own N7b infra *is* the row-side
block-triangular route, and the only new obligation is the honest eq. (6.12) row equality.

**Next concrete commit (post-this-recon).** The **first Lean node of stratum 1** — the eq. (6.12) producer
behind `lem:case-II-realization-placement`, cut leaf-most-first per the node order in `notes/Phase22c.md`
*Hand-off* (the new red leaf is the placement `p₁` + `hrow`; everything else is green N7b infra). Re-recon
the `hrow` row-equality specifically at the build's open (it is the structural-fidelity crux). The
D-candidate crux (strata 2–3) gets its math-first decomposition when its sub-phase opens.

### 1.28 Phase 22c, fourth pass — SIGNATURE-LEVEL verification of the stratum-1 cut against the real Lean signatures, before any build (2026-06-05)

Fourth docs-only commit (no Lean / `\leanok` / blueprint). The user asked for one more
design pass *before* the stratum-1 build: a **signature-level** node-level constructibility
recon (`DESIGN.md` *Constructibility recon … 2nd/3rd halves*) of the single genuinely-new
brick (`p₁` + `hrow`) against the **actual current Lean signatures** of the green bricks it
composes with — the one place a build surprise could hide. **Outcome: the composition
verifies cleanly. No mismatch.** The critical check (does N7b-2's `hrow` accept the
`p₁(vb)=q(ab)` degenerate-placement reproduction as its discharging term?) passes, for a
structural reason pinned below. The recorded signatures + per-obligation discharge + the
precise new-brick statement follow; the *Hand-off* in `notes/Phase22c.md` is the build
agent's leaf-most-first target.

**The five green bricks, exact current signatures (verbatim heads).**
- **N7b-1** `Pinning.lean:265` `BodyHingeFramework.exists_independent_panelRow_subfamily_of_edge`
  `(F : BodyHingeFramework k α β) {ends} {e : β} (huv : (ends e).1 ≠ (ends e).2)
  (he : F.supportExtensor e ≠ 0) : ∃ s, (∀ i ∈ s, i.1 = e) ∧ Nat.card s = screwDim k - 1 ∧
  LinearIndependent ℝ (fun i : s => F.panelRow ends i)`. Gives `D−1` rows, all on edge `e`.
- **N7b-0** `GenericityDevice.lean:476`
  `BodyHingeFramework.exists_independent_panelRow_subfamily_of_rigidOn`
  `(F) {ends} (hends : ∀ e, F.graph.IsLink e (ends e).1 (ends e).2) (hne : ∀ e, F.supportExtensor e ≠ 0)
  (hnev : F.graph.vertexSet.Nonempty) (hrig : F.IsInfinitesimallyRigidOn F.graph.vertexSet) :
  ∃ s, Nat.card s = screwDim k * (F.graph.vertexSet.ncard - 1) ∧ LinearIndependent ℝ (fun i : s => F.panelRow ends i)`.
  Gives `D(|V|−1)` rows from rigidity *on its own vertex set*. NB: this is `D·(|V(G_v^{ab})|−1)`
  — for the split-off graph `|V(G_v^{ab})| = |V(G)|−1`, so it supplies `D(|V(G)|−2)` = the old block. ✓
- **N7b-2** `GenericityDevice.lean:354` `PanelHingeFramework.exists_independent_panelRow_transport`
  `(G₁ G₂ : Graph α β) (ends₁ ends₂) (q₁ q₂) {s₁ s₂} (f : s₂ → s₁) (hf : Function.Injective f)
  (hrow : ∀ i : s₂, (ofNormals G₂ ends₂ q₂).toBodyHinge.panelRow ends₂ i
      = (ofNormals G₁ ends₁ q₁).toBodyHinge.panelRow ends₁ (f i))
  (hindep : LinearIndependent ℝ (fun i : s₁ => (ofNormals G₁ ends₁ q₁).toBodyHinge.panelRow ends₁ i)) :
  LinearIndependent ℝ (fun i : s₂ => (ofNormals G₂ ends₂ q₂).toBodyHinge.panelRow ends₂ i)`.
- **N7b-3** `RigidityMatrix.lean:548` `linearIndependent_sum_pinned_block`
  `[DecidableEq α] {v : α} {rn : ιn → Module.Dual ℝ (α → ScrewSpace k)} {ro : ιo → …}
  (hold : ∀ (j : ιo) (x : ScrewSpace k), ro j (Function.update 0 v x) = 0)
  (hnewpin : LinearIndependent ℝ (fun i : ιn => (rn i).comp (LinearMap.single ℝ (fun _ : α => ScrewSpace k) v)))
  (holdindep : LinearIndependent ℝ ro) : LinearIndependent ℝ (Sum.elim rn ro)`.
- **N7a (closure)** — TWO usable forms. (a) `GenericityDevice.lean:313`
  `PanelHingeFramework.hasFullRankRealization_of_independent_panelRow (G) (ends)
  (hends : ∀ e, G.IsLink e (ends e).1 (ends e).2) (hne : V(G).Nonempty) {q₀} {s}
  (hindep : LinearIndependent ℝ (fun i : s => (ofNormals G ends q₀).toBodyHinge.panelRow ends i))
  (hcard : screwDim k * (V(G).ncard - 1) ≤ Nat.card s) : HasFullRankRealization k G` — wants a `Set s`
  index. (b) `CaseI.lean:1631`
  `BodyHingeFramework.isInfinitesimallyRigidOn_vertexSet_of_independent_rigidityRows (F) {ι} [Finite ι]
  {a : ι → Module.Dual ℝ …} (hLI : LinearIndependent ℝ a) (hmem : ∀ i, a i ∈ F.rigidityRows)
  (hne) (hcard : screwDim k * (F.graph.vertexSet.ncard - 1) ≤ Nat.card ι) :
  F.IsInfinitesimallyRigidOn F.graph.vertexSet` — takes an **arbitrary** `ι`-indexed family (so a
  `Sum`-index feeds it directly) + a `hmem`-membership-in-`rigidityRows` side-goal, then the device
  lift is the final `hasFullRankRealization_of_independent_panelRow` step (no `Set s` repackage). **Form
  (b) is the cleaner closure for stratum 1**, because N7b-3 hands back a `Sum.elim`-indexed family, not
  a `Set s`. This is exactly the closure path the green Case-I composer uses (`CaseI.lean:1794–1831`).

**THE CRITICAL CHECK — does N7b-2's `hrow` accept the `p₁(vb)=q(ab)` reproduction? YES.** `hrow i`
is the *per-row equality* `panelRow` of `ofNormals G₂ ends₂ q₂` at `i` `=` `panelRow` of
`ofNormals G₁ ends₁ q₁` at `f i`. The structural fact that discharges it (verified against the real
defeq chain):
- `panelRow F ends i = hingeRow (ends i.1).1 (ends i.1).2 (annihRow (F.supportExtensor i.1) i.2.1 i.2.2)`
  (`Pinning.lean:46`), and
- `(ofNormals G ends q).toBodyHinge.supportExtensor e
  = panelSupportExtensor (q-as-normal (ends e).1) (q-as-normal (ends e).2)`
  (`toBodyHinge_supportExtensor` `PanelHinge.lean:94` ∘ `ofNormals_normal` `PanelHinge.lean:267`,
  both `rfl`).

So **`panelRow` of `ofNormals G ends q` at `i` depends only on `ends` and `q` — NOT on `G`.** This is
the load-bearing structural fact (the N7b-2 docstring states it: "the panel support extensor reads only
`ends` and `q`, not the graph — `toBodyHinge_supportExtensor`"). Consequence for stratum 1: set
`G₂ := G`, `G₁ := G_v^{ab}`, `q₂ := q₁ := q₀` (one shared seed), and pick `ends₂ = ends_G`,
`ends₁ = ends_{G_v^{ab}}` to **agree on every common-subgraph edge** (the `e₀`-free edges of `G−v`);
then for each old-block index `i` (whose edge is a `G−v` edge), `ends₂ i.1 = ends₁ (f i).1` and
`q₂ = q₁`, so both sides of `hrow i` are the *same* `panelRow` term and `hrow i := rfl`. The
`p₁(vb)=q(ab)` reproduction is **not** what N7b-2's `hrow` consumes — N7b-2 transports the **old block**
(the `D(|V|−2)` `e₀`-free rows of `G−v`), and `hrow` there is the trivial `ends`/`q`-agreement `rfl`.
**The `p₁(vb)=q(ab)` row reproduction is the NEW-block content, and it does not flow through N7b-2 at
all** — it is what makes the `vb`-row of `R(G,p₁)` land in `v`'s screw column so N7b-3's pin-a-body
split (`hold`/`hnewpin`) separates it from the old block. (See the corrected obligation statement below
— this is a *refinement* of `notes/Phase22c.md` *Hand-off* step 1's "`hrow` IS the eq. (6.12)
reproduction", which conflated the two roles; flagged + corrected here, not a blocker.)

**The other compositions type-align (each checked).**
- *N7b-1 count + index.* `Nat.card s = screwDim k - 1 = D−1`, all rows on the **new** edge(s) `va`/`vb`
  (the `i.1 = e` conjunct). To feed N7b-3's `hnewpin` (independence *of the comp with `single … v`*),
  the new rows must be independent **as functionals of `v`'s screw column** — N7b-1 gives raw `panelRow`
  independence; the `.comp (single … v)` step is a *new* small obligation (see new-brick statement). The
  `D−1` count matches KT eq. (6.12)'s `+(D−1)`. ✓
- *N7b-0 count + rigidity input.* Needs `F.IsInfinitesimallyRigidOn F.graph.vertexSet` for
  `F = (ofNormals G_v^{ab} ends₁ q₀).toBodyHinge`. The IH from `theorem_55.hsplit`'s premise is
  `HasFullRankRealization k (G.splitOff v a b e₀)`; `exists_rigidOn_ofNormals_of_hasFullRankRealization`
  (`GenericityDevice.lean:1078`) repackages it to *exactly* `∃ ends₁ q, (ofNormals G_v^{ab} ends₁ q).toBodyHinge.IsInfinitesimallyRigidOn V(G_v^{ab})`.
  So the IH supplies N7b-0's `hrig` directly (modulo putting it on the **shared** seed `q₀` — the
  single-seed coupling, below). At `k=0` the IH is full rank on `V(G_v^{ab})`, and `|V(G_v^{ab})| =
  |V(G)|−1` (`vertexSet_splitOff` `Operations.lean:599`, `V = V(G)\{v}`), so N7b-0 yields `D·(|V(G)|−2)`
  old rows. ✓
- *N7b-3 block split.* `rn` := the `D−1` new rows, `ro` := the `D(|V|−2)` transported old rows.
  `hold j x` (old rows vanish at `update 0 v x`): the old rows' edges avoid `v` (they are `G−v` edges, so
  `hingeRow`'s two endpoints are both `≠ v`, and `hingeRow u w r (update 0 v x) = r(0−0) = 0`). `hnewpin`:
  the new rows independent after `.comp (single … v)`. `holdindep`: N7b-2's output. Output: `Sum.elim rn ro`
  independent. **This matches KT eq. (6.16)'s block-triangular column ops exactly** (new rows in `v`'s
  column, old rows off it). ✓
- *N7a closure.* Form (b) consumes `Sum.elim rn ro` (the `ι := ιn ⊕ ιo` family) + `hmem : ∀ i, family i ∈ rigidityRows`
  (each row's edge links in `G` — new edges `va`/`vb` ∈ E(G), old edges are `G−v` ⊆ `G`) + the card bound
  `D(|V(G)|−1)−1 ≤ Nat.card (ιn ⊕ ιo)`. **Count: `(D−1) + D(|V(G)|−2) = D(|V(G)|−1)−1`** — *one short* of
  `D(|V(G)|−1)`, the Case-III missing row (strata 2–3). So stratum 1 cannot use the `≥ D(|V|−1)` form of
  N7a; it produces a `rank ≥ D(|V|−1)−1` lower-bound brick, **not** `HasFullRankRealization`. This is the
  honest deliverable (lower bound toward the red node), confirmed by the count. ✓

**Reuse from 22b — re-confirmed NOT applicable (the prior recon stands).** 22b's `degeneratePlacement`
(`CaseI.lean:868`), `extProj`, `panelRow_collapseTo_comp_extProj_dualMap` implement a **block collapse**
of an entire rigid block `V(H)→r` with an exterior-column *projection*. Stratum 1 is a **single-vertex**
placement (`p₁(vb)=q(ab)`) reproducing **one** row, with **no** projection — the block-triangularity is
the pin-a-body split N7b-3, not a projected complement. §1.27's verdict is correct: not reused now.

**THE NEW BRICK — precise proof obligation (signature-checked).** The single genuinely-new Lean content
is the placement `p₁` + two row facts. State it as one producer (working name
`PanelHingeFramework.case_II_placement_eq612` / `…_independent_panelRow`), built leaf-most:
1. **The shared seed + selectors.** A free normal assignment `q₀ : α × Fin (k+2) → ℝ` and two endpoint
   selectors `ends_G : β → α × α` (for `G`), `ends₁ : β → α × α` (for `G_v^{ab}`) that (i) record their
   graph's links (`hends`), (ii) **agree on every `e₀`-free common edge** so N7b-2's `hrow` is `rfl`, and
   (iii) place `v`'s `b`-edge `e_b`'s far endpoint reading at the `e₀=ab` hinge so the `vb`-row reproduces
   the `e₀`-row. The eq. (6.12) data `p₁(va)=L⊂Π(a)`, `p₁(vb)=q(ab)` is encoded as the value of `q₀` at
   `v`'s coordinates (`q₀(v,·)`) chosen so `supportExtensor e_b = panelSupportExtensor (q₀ v) (q₀ b)`
   equals the `e₀`-hinge extensor `panelSupportExtensor (q₀ a) (q₀ b)` — i.e. `q₀ v` is placed on the line
   `L ⊂ Π(a)` making `panel(v) = panel(a)` along the `b`-hinge. **This is the eq. (6.12) geometric
   content** and the only genuinely-new construction.
2. **`hnewpin` (the new-block column independence).** From N7b-1's `D−1` raw-independent new rows on
   `e_b` (or `e_a`), show they remain independent after `.comp (LinearMap.single ℝ _ v)` — i.e. the new
   rows are independent *as read through `v`'s screw column*. Since each new row is `hingeRow v (other) r`
   and `hingeRow v w r ∘ single v = r ∘ (screwDiff v w ∘ single v) = r` (the `single v` puts the test
   screw on `v`, the other endpoint reads `0`), this is essentially `linearIndependent_hingeRow_star`'s
   pin-at-`v` argument restricted to the single new edge — a bounded, buildable step (N7b-1 + a
   `hingeRow`-comp-`single` identity). **This is the second new fact** (small).
3. **`hrow`-`rfl` for the old block.** Discharge N7b-2's `hrow i := rfl` from the `ends`/`q₀` agreement on
   `G−v` edges (step 1.ii) — `panelRow` reads only `ends`/`q₀`, not the graph. The selector `f : s₂ → s₁`
   is the identity-on-common-edges injection (drops the `e₀` index). **`rfl`, given the agreement.**
4. **Assemble + close.** N7b-1 → `hnewpin` (step 2); N7b-0 (on the IH `hrig` at `q₀`) → N7b-2 (`hrow`
   from step 3) → `holdindep`; N7b-3 → `Sum.elim` independence; N7a form (b) with the `hmem` membership +
   the `D(|V|−1)−1` card bound → the lower-bound deliverable. The deliverable is a `rank R(G,p₁) ≥
   D(|V(G)|−1)−1` brick (equivalently: an independent `panelRow` family of size `D(|V(G)|−1)−1` on the
   shared seed `q₀`), explicitly **not** `HasFullRankRealization` (one row short).

**Single design refinement flagged (conservative choice made, not a blocker).** `notes/Phase22c.md`
*Hand-off* step 1 said "`hrow` IS the eq. (6.12) reproduction." The signature trace shows the eq. (6.12)
`p₁(vb)=q(ab)` reproduction is the **new-block** content (it makes the `vb`-row reproduce the `e₀`-row so
it lands in `v`'s screw column, feeding `hnewpin`/N7b-3), while N7b-2's `hrow` is the **old-block**
`ends`/`q₀`-agreement `rfl`. Conservative correction: the two are distinct roles; the new brick owns the
reproduction (step 1.iii + step 2), N7b-2's `hrow` is the trivial old-block agreement (step 3). The
*Hand-off* in `notes/Phase22c.md` is updated to this split. No new node is needed — the count and the
composition are unchanged; only the labelling of which obligation carries the reproduction is corrected.

**Net.** The stratum-1 composition is signature-verified clean: N7b-0/1/2/3 + N7a form (b) compose with
the new `p₁`+`hnewpin`+`hrow`-`rfl` brick; the count `(D−1)+D(|V|−2)=D(|V|−1)−1` closes from the named
green inputs; the IH from `hsplit` feeds N7b-0 via `exists_rigidOn_ofNormals_of_hasFullRankRealization`.
The one genuinely-new construction is the eq. (6.12) shared-seed selector (step 1), plus the bounded
`hnewpin` column-independence (step 2); `hrow` is `rfl`. Ready to build leaf-most-first.

### 1.29 Phase 22c, fifth pass — step-1 constructibility recon: the single-seed coupling RESOLVED + the placement geometry pinned (the planning gate before the build, 2026-06-05)

Fifth docs-only commit (no Lean / `\leanok` / blueprint). The user's standing direction for Phase 22c
— *"this is a very intricate part of the proof; never dispatch a build before the plan is clear"* —
applied to the one piece §1.28 left at the *requirements* level, not the *construction* level: **step 1,
the shared-seed selector geometry**, the "only genuinely-new construction." §1.28's N7b-0 bullet deferred
reconciling the IH's *existential* seed with the *single* shared `q₀` to "the single-seed coupling,
below" — and never wrote the "below." A focused read-only recon against the live defs resolves both that
gap and the concrete placement; every signature below was re-verified at the cited line.
**Verdict: PLAN CLEAR — no build surprise hidden in step 1.**

**(A) The single-seed coupling — SOUND, via a green lemma (not hand-waved).** The IH from
`theorem_55.hsplit` repackages (`exists_rigidOn_ofNormals_of_hasFullRankRealization`,
`GenericityDevice.lean:1078`) to `∃ ends₁ q, (ofNormals G_v^{ab} ends₁ q).toBodyHinge.IsInfinitesimallyRigidOn V(G_v^{ab})`.
Build the shared seed by overriding only the fresh vertex: `q₀ := Function.update q v (placement)`
(`ofNormals` takes `q : α × Fin (k+2) → ℝ`, so `q₀(v,·) : Fin (k+2) → ℝ` is the curried slice). This
leaves the **old block untouched**: the IH rigidity `IsInfinitesimallyRigidOn V(G_v^{ab})`
(`RigidityMatrix.lean:752`) quantifies only over `V(G_v^{ab}) = V(G)\{v}` (`vertexSet_splitOff`,
`Operations.lean:599`) and its motions read only `G_v^{ab}` edges — **all avoiding `v`** (splitting-off
removes `v`). The Lean lever is the green `toBodyHinge_withNormal_infinitesimalMotions_eq`
(`PanelHinge.lean:594`), whose `hv` hypothesis (`v` is an endpoint of no `P.graph` edge) holds **exactly
because** `v ∉ V(G_v^{ab})`; `ofNormals_withGraph` (`PanelHinge.lean:459`, `rfl`) swaps `G_v^{ab}→G`. So
the IH rigidity at `q₀` feeds N7b-0's `hrig` directly. N7b-3's `hold` (old rows vanish at `update 0 v x`)
holds for the same reason — every old edge's `hingeRow` endpoints are `≠ v`.

**(B) The placement of `q₀(v,·)` — `n_a + t·n_b` with `t ≠ 0` (NOT `q₀ v = q₀ a`).** Write `n_a := q(a,·)`,
`n_b := q(b,·)`; set `q₀(v,·) := n_a + t·n_b`, `t ≠ 0` (concretely `t = 1`). With `panelSupportExtensor
n₁ n₂ = complementIso (normalsJoin n₁ n₂)` (`PanelLayer.lean:161`) and `normalsJoin = ιMulti ℝ 2 ![·,·]`
(`PanelLayer.lean:64`, alternating):
- `normalsJoin (n_a + t·n_b) n_b = normalsJoin n_a n_b` (the `t·n_b` term wedges `n_b∧n_b = 0`), so
  `panelSupportExtensor (q₀ v)(q₀ b) = panelSupportExtensor (q₀ a)(q₀ b)` — the **`vb`-row reproduces the
  `e₀=ab`-row** (≠ 0: the IH's `e₀` hinge is transversal, `q a, q b` independent, `panelSupportExtensor_ne_zero_iff`
  `PanelLayer.lean:172`). This is N7b-1's `he` input on `e_b`.
- `normalsJoin (n_a + t·n_b) n_a = −t·normalsJoin n_a n_b`, so `panelSupportExtensor (q₀ v)(q₀ a) =
  −t·panelSupportExtensor (q₀ a)(q₀ b) ≠ 0` for `t ≠ 0` — the **`va`-hinge stays a nondegenerate line**
  `L ⊂ Π(a)` (KT eq. (6.12)).

  **The `t = 0` trap.** `q₀(v,·) := q₀(a,·)` (= `n_a`) still gives the `vb`-reproduction (so stratum 1's
  *count* would close — the `D−1` new rows come from `e_b` alone via N7b-1, and the form-(b) closure
  needs only `hmem ∈ rigidityRows`), **but it zeros the `va`-hinge** (`panelSupportExtensor n_a n_a = 0`,
  `extensor_eq_zero_of_eq`), building a *degenerate* candidate. Since stratum 1 is meant to **set up the
  KT candidate scaffold the crux strata complete** (*Sub-phase scope cut*, `notes/Phase22c.md`), and `t≠0`
  costs stratum 1 nothing (the `va` edge is not referenced in its count), use `t ≠ 0` for fidelity to KT's
  actual eq. (6.12) candidate — `DESIGN.md` *Match the source's argument structure, not just its conclusion*.
  (If a `t≠0` statement proves awkward, `t=0` is a sound fallback for the lower-bound brick *alone*,
  deferring the `va`-line to the crux — flagged, not chosen.)

**(C) Sub-lemma cut (all bounded).**
1. The wedge-bilinearity placement lemma in `PanelLayer.lean`: `normalsJoin (n_a + t•n_b) n_b =
   normalsJoin n_a n_b` (+ the two `panelSupportExtensor` (in)equalities). A few lines from
   `AlternatingMap.map_update_add`/`map_smul` + `map_eq_zero_of_eq`; no fused panel-layer lemma exists yet.
2. The `withNormal`/`withGraph` glue relating `ofNormals G ends q₀` to the `withNormal`-updated IH
   framework (uncurry of `Function.update`) — definitional / `rfl`-adjacent.
3. The producer `PanelHingeFramework.case_II_placement_eq612` (lands near N7b-1 in `Pinning.lean`),
   assembling N7b-1 → `hnewpin` (LANDED, `linearIndependent_panelRow_comp_single_of_edge`) → N7b-0 →
   N7b-2 (`hrow := rfl`) → N7b-3 (`linearIndependent_sum_pinned_block`) → N7a form (b), yielding the
   `rank R(G,p₁) ≥ D(|V|−1)−1 = 6|V|−7` lower-bound brick (explicitly NOT `HasFullRankRealization` — one
   row short, the Case-III missing row deferred to strata 2–3).

**(D) Precedent.** The green Case-I composer (`CaseI.lean:1754–1831`) already builds the analogous shared
seed (one `q₀`, one `F = ofNormals G ends q₀`), splits rows into two blocks, proves union independence via
`Sum.elim` (`linearIndependent_sum_pinned_block`), supplies `hmem`, closes with form (b). Step 1 mirrors
it; the second block is a single re-inserted vertex, so the `withNormal` 1-extension replaces Case I's
contraction/`extProj` machinery (22b's `degeneratePlacement`/`extProj` confirmed not reused, §1.27/§1.28).

### 1.30 Phase 22d, footnote-6 kernel recon — eq. (6.22) is NOT a green re-exposure; the genuinely-new content is a `non-root-from-algebraic-independence` brick (2026-06-06)

A "size the kernel" re-test of the prior Gap-3 verdict (`notes/Phase22d.md` *Gap 3
recon*), against the **actual** current signatures (the user flagged that the Gap-3
recon cited the *bare* `HasFullRankRealization`, while 22b strengthened the
generic-case motive). The hypothesis under test: eq. (6.22) re-exposes from green
21b/22b machinery, the kernel collapsing to footnote 6 = "the Phase-21b device run
in the direction we haven't exposed." **Verdict: refuted on the bottom line, but two
of its three structural claims confirmed.** Verified by lean-lsp/Read against the
real defs; no Lean / `\leanok` / blueprint edits (decision-support, like §1.4–§1.29).

**The three structural claims.** (a) *matroid↔row link is the IH, not a separate
iso* — **CONFIRMED**: the only bridge is `rigidityMatrix_prop11` (`PanelHinge.lean:1176`),
abstract, taking the rank bounds `hub`/`hgen` as hypotheses; its doc-comment names
the Phase-21b device as the thing selecting the max-attaining point. (b) *step ③
(redundancy from the count) is pure LA given (6.18)+(6.22)* — **CONFIRMED**
(pigeonhole over the `D−1` `ab`-rows with corank `k' ≤ D−2`; the rank-nullity
template is `isInfinitesimallyRigidOn_ofNormals_of_rankPolynomial_ne_zero`'s body).
(c) *eq. (6.22) re-exposes from the device* — **REFUTED**.

**Why (c) is refuted, pinned to signatures.** The 22b motive
`HasGenericFullRankRealization` (`PanelHinge.lean:968`) added `Q.IsGeneralPosition`
+ link-recording but is **still `∃ Q`** (existence). `IsGeneralPosition`
(`:120`) is **only** `∀ a≠b, LinearIndependent ![normal a, normal b]` — degree-1
pairwise transversality, NOT non-root-ness of the rank polynomial. The device has
*two* halves: the producer `exists_rankPolynomial_of_rigidOn{_linking_set}`
(`GenericityDevice.lean:1112/1288`, from a rigid seed `q₀` ⟹ `∃ Q, eval q₀ Q ≠ 0 ∧
∀ non-root ⟹ LI`) and the consumer
`isInfinitesimallyRigidOn_ofNormals_of_rankPolynomial_ne_zero{_linking_set}`
(`:1378/1517`, **given `eval q Q ≠ 0` ⟹ rigid at that `q`**, no GP needed). So the
consumer *already runs the given-point direction* — the gap is proving `eval q Q ≠ 0`
for the specific `Q`. footnote 6 supplies this from *algebraic independence of the
seed over ℚ*, and **the project has zero `AlgebraicIndependent`/transcendence
machinery** (grep-confirmed tree-wide; the only non-zero-at-a-point brick is
`MvPolynomial.exists_eval_ne_zero`, which gives *∃ a* non-root, never a *given* one).

**The genuinely-new content, named exactly.** A `non-root-from-algebraic-independence`
brick = **(i)** mirrorable `MvPolynomial.eval_ne_zero_of_algebraicIndependent` (alg.-indep.
tuple ⟹ off every nonzero ℚ-polynomial's zero locus; mathlib has `AlgebraicIndependent`
API, so half is upstream-flavored) + **(ii)** a seed-alg-indep invariant threaded
through the induction (NEW; may need a *third* motive form alongside the 22b GP +
link-recording strengthenings). Then the kernel `lem:case-III-seed-rank-bridge`
(`corank R(ofNormals G_v ends q|_{E_v}) = def(G̃_v)`) composes (i)+(ii) with the
device consumer + `rigidityMatrix_prop11`. **eq. (6.18) (full rank of `R(G_v^{ab},q)`)
is NOT separately in hand** — 22c's `case_II_placement_eq612` (`CaseI.lean:2331`) is
the `≥ D(|V|−1)−1` lower-bound brick; the full `D(|V|−1)` *is* the Claim-6.11 `+1`.

**Net (build queue unchanged).** This refines the prior verdict from "irreducible
kernel" to "irreducible kernel = a *named* `non-root-from-alg-indep` brick"; it does
**not** overturn it (unlike the Gap-2 overturn, the strengthening here is the wrong
*kind* of content). The next build stays the Gap-3 combinatorial shell
`splitOff_removeVertex_minimalKDof`; the kernel (likely merged with Gap 1) is a
later dedicated math-first sub-phase, carried-as-hypothesis. Full Q1–Q5 in
`notes/Phase22d.md` *Footnote-6 kernel recon (2026-06-06)*.

### 1.31 Phase 22d, kernel-route decision + the algebraic-independence relaxation tracker (2026-06-06)

§1.30 named the kernel as genuinely-new content; its default was carry-as-hypothesis.
**User decision (2026-06-06): build the algebraic-independence route DIRECTLY to fully
green** (the certain path = KT's actual argument), NOT carry-as-hypothesis and NOT the
unverified product-route shortcut — superseding §1.30's "carried-as-hypothesis" tail.
The product-route shortcut (choose the seed at the Claim-6.11 composition as a non-root
of the *finite product* of the nested IH rank polynomials, avoiding alg-independence at
`d=3`) is captured as a deferred **relaxation TODO**, with a tracker of *every*
molecular-program site that leans on algebraic independence (the genericity
device/Claim 6.4 *avoided* it; the 22d kernel is the *first forced* site; Phase 23
likely), in the standing note **`notes/AlgebraicIndependence.md`** (the single source —
not duplicated here). Full decision + effect-on-plan: `notes/Phase22d.md` *Kernel-route
decision (2026-06-06, user)*.

### 1.32 Phase 22d, kernel sub-phase (ii) opening recon — the seed-genericity invariant SPLITS into a motive conjunct (ii-a) plus a *rationality bridge* (ii-b) the §1.30 cut missed (2026-06-06)

The math-first recon mandated at the (ii) node's open (`notes/Phase22d.md`
*Hand-off*: "confirm whether (ii) needs a third motive form … or threads onto the
existing `HasGenericFullRankRealization`"). Read leaf (i)
(`AlgebraicIndependent.aeval_ne_zero`) against the *actual* device producer/consumer
signatures (`GenericityDevice.lean:1112`/`:1378`) and the polynomial-coordinate chain
(`PanelLayer.lean` `annihRowPoly`/`panelSupportPoly`). Decision-support; no Lean /
`\leanok` / blueprint edits (like §1.4–§1.31).

**What (iii) must compose, traced through the real signatures.** The kernel
`lem:case-III-seed-rank-bridge` fires the device *consumer*
`isInfinitesimallyRigidOn_ofNormals_of_rankPolynomial_ne_zero` at the **inductively-fixed
seed `q`** — i.e. it needs `MvPolynomial.eval q Q ≠ 0` for the device producer's `Q`
(`exists_rankPolynomial_of_rigidOn` gives `Q : MvPolynomial σ ℝ` with `eval q₀ Q ≠ 0` at
the *producer's own* rigid seed `q₀`, plus the non-root ⟹ LI clause). Leaf (i) supplies
`eval`-non-root-ness from `q`'s algebraic independence over ℚ — **but only for a polynomial
over ℚ** (`aeval q : MvPolynomial σ ℚ → ℝ`). Two distinct impedances surface; (i) closes
neither alone.

**Verdict: (ii) is NOT a single leaf and NOT pure motive-strengthening — it SPLITS.**
- **(ii-a) the seed-genericity motive conjunct** [the part §1.30 anticipated]. The
  realizing seed `q` must be algebraically independent over ℚ at the composition point, so
  the kernel has an alg-indep `q` in hand. This is a third motive guarantee, **paralleling
  22b's GP / link-recording** strengthenings (an extra conjunct on
  `HasGenericFullRankRealization`, or a third sibling motive). Producers must build their
  `ofNormals G ends q₀` at an alg-indep seed and carry the conjunct; the moment-curve seed
  (`withMomentNormals`, `GenericityDevice.lean:~1785`) is the natural candidate alg-indep
  point — **confirm it is provably alg-indep over ℚ, or substitute a transcendental basis**
  (open).
- **(ii-b) the rationality bridge** [NEW — the §1.30 cut missed this]. Leaf (i) needs the
  rank polynomial over **ℚ**, but the device's `Q` is typed over **ℝ**
  (`exists_polynomial_ne_zero_of_linearIndependent_at`, `Mathlib/.../Rank.lean:474`, builds
  `Q := det` of a submatrix of the coordinate family `c`). `c = ± annihRowPoly`, and
  `annihRowPoly` bottoms on `panelSupportPoly` (`PanelLayer.lean:385`) whose coefficients are
  `MvPolynomial.C r` with `r : ℝ` a `complementIso`-`repr` structural constant — **rational
  (±1 / fixed change-of-basis entries) mathematically, but ℝ-typed and not manifestly
  rational in the term.** So `eval q Q = aeval q Q₀` needs `Q = MvPolynomial.map (algebraMap
  ℚ ℝ) Q₀` for some `Q₀ : MvPolynomial σ ℚ`, plus `Q ≠ 0 ⟺ Q₀ ≠ 0` (`map` along an injective
  ring hom). **Grep-confirmed: the molecular tree has ZERO `algebraMap ℚ ℝ` / `MvPolynomial.map`
  scaffolding** — this is a genuinely-new obligation, invisible to §1.30 (which named only
  "(ii) = seed-alg-indep invariant").

**Why (ii-b) is the load-bearing surprise.** The two cuts diverge on cost: a pure motive
conjunct (ii-a alone) is 22b-shaped plumbing; (ii-b) forces either (b1) re-typing the whole
device coordinate chain `panelSupportPoly → annihRowPoly → c → Q` over a base ring `R` with
`algebraMap R ℝ` and instantiating `R = ℚ` (invasive — touches every producer), or (b2) a
*post-hoc* "`Q`'s coefficients lie in `range (algebraMap ℚ ℝ)`" descent on the already-built
ℝ-polynomial (`MvPolynomial.eval q Q = aeval q (Q.descend)` when every `coeff` is rational),
needing a `complementIso`-entries-are-rational lemma (the structural-constant rationality KT
takes for granted). **(b2) is the lighter cut** (no producer re-type; one descent lemma + the
`complementIso`-rationality fact) and is the recommended first attempt; (b1) is the fallback
if the descent's coefficient bookkeeping proves worse than a clean re-type.

**Net effect on the build queue.** (ii) is re-cut into **(ii-a)** [motive conjunct, 22b-shaped]
+ **(ii-b)** [rationality bridge: a `complementIso`-rational-entries leaf ⊕ the `Q`-descent
mirror]. (iii) `lem:case-III-seed-rank-bridge` then composes (i) ⊕ (ii-a) ⊕ (ii-b) with the
consumer + `rigidityMatrix_prop11`. The next *build* commit is the leaf-most of (ii-b): the
descent mirror `MvPolynomial.eval = aeval ∘ descend` for a coefficient-rational ℝ-polynomial
(or its `MvPolynomial.map` half), which is **upstream-eligible** and provable independent of
all the molecular geometry — a true leaf, unlike (ii-a) which waits on the moment-curve
alg-independence question. Full Q&A + the leaf order: `notes/Phase22d.md` *Kernel sub-phase
(ii) recon*.

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

### Assembly (may defer to Phase 23)

- **`prop:rigidity-matrix-prop11` `hub` brick** — `research-shaped (multi-commit)`,
  Track-independent (Phase-19 partition count: construct `D(|P|−1)−(D−1)·d_G(P)`
  motions from a deficiency-attaining partition). Decompose math-first before
  scheduling.
- **`thm:theorem-55` / `lem:case-III` flip green** once the producers land
  (one-line, the recursion body is already assembled).

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
