# Phase 22 — realization-layer design (decision-support doc)

> **ARCHIVED — closed-phase reference (Phase 22 closed; do not read whole).**
> This is the Phase-22 realization-layer design recon. **~40 inbound `§`-pointers**
> cite it (`DESIGN.md`, `BlueprintExposition.md`, `ROADMAP.md`, `blueprint/CLAUDE.md`,
> the Phase-22* notes, Lean doc-comments under `Molecular/`). Reach a specific `§` via
> its inbound pointer and read that section — do not read the file whole (≈8.5k lines).

> **Compression status (Phase 29 / RETRO, W2-7).** §0–§1.49 (the motive decision +
> the `d=3` producer's crux architecture through the GAP-4 interface design) were
> shrunk to ≤3-line-verdict form on 2026-07-09 (**W2-7**, first slice) — every cited
> heading in that range survives, zero repoints. §1.50 onward (the `hcand` discharge
> through the L10 signature pin — the general-`d`/all-`k` restructure, the bulk of
> the file) still carries the full narrative, pending a **follow-up W2-7 slice**
> (`notes/Phase29.md` *W2 slice plan*). Once that lands, this doc's role is a
> compressed verdict archive; the blow-by-blow lives in git history and the
> Phase-29 retrospective appendix (`blueprint/src/chapter/retrospective.tex`). No
> live Phase-23 working material lives here: the §1.33(C)–(E) reuse map was lifted
> to `notes/MolecularConjecture.md` *Reuse map*, and distilled cross-cutting
> lessons live in `DESIGN.md`.

> **File-layout note (pre-Phase-22b structure pass, `notes/Phase22-structure.md`).**
> `AlgebraicInduction.lean` → `Molecular/AlgebraicInduction/` (`PanelLayer`/`Pinning`/
> `PanelHinge`/`GenericityDevice`/`CaseI`); `Induction.lean` → `Molecular/Induction/`
> (`Operations`/`SplitOffDeficiency`/`ReducibleVertex`/`Contraction`/`ForestSurgery`).
> Inline `….lean:NNNN` line anchors below predate the split.

**Status:** design pass, not a build plan. Produced 2026-06-04–06-07 after the
constructibility recon (FRICTION dead-end #5) found the Case-I coupling had two real
gaps: **(G1)** the motive lacked general position (KT's "nonparallel"), **(G2)** the
joint algebraic independence the simple cases need. Resolved by the two-motive split
(§1.4) and closed out through the `d=3`-assembly opening recon (§1.33), handing off to
Phase 22g/23.

Primary sources: KT 2011 §5–§6.4 (`.refs/`, printed pp. 669–697);
`Molecular/{AlgebraicInduction,Extensor,Deficiency,Induction}.lean`;
`blueprint/src/chapter/algebraic-induction.tex` Case I/II/III + `thm:theorem-55`;
`notes/Phase21b.md` *Finding A/B*; `DESIGN.md` (*Realization motive must be
`V(G)`-relative*, *Constructibility recon …*, *Phase Case-naming …*).

---

## 0. The crux, in one paragraph

KT Theorem 5.5 (p. 669) reads: *"there exists a **(nonparallel, if `G` is simple)**
panel-hinge realization satisfying `rank R(G,p) = D(|V|−1)−k`."* Every inductive case
invokes the IH in this same `∃ nonparallel realization` form. Three places consume the
incoming legs' nonparallel-ness: Claim 6.4's polynomial coordinatization (needs
transversal hinges), Lemma 6.3/6.5's boundary-panel intersection (a genuine
`(d−2)`-flat only when transversal), and the simple cases' joint algebraic
independence over ℚ. The project's motive was **bare** (no general-position promise)
— mismatch (G1); the joint-genericity is (G2). Both intrinsic to KT's argument, not
Lean artefacts; both resolved below.

---

## 1. Motive decision

### 1.1 What KT Theorem 5.5 actually guarantees

Settled: the strengthened motive must add `Q.IsGeneralPosition` when `G.Simple`
(unconditional GP fails at the parallel-K₂ base) — strengthen only conditioned on
simplicity. Durable: `HasFullRankRealization`/`IsGeneralPosition` defs; resolved via
the two-motive split, §1.4.

### 1.2 What each producer needs from / supplies to the motive

Settled: the green producer infra already demands `hne`/`hgp` as hypotheses; the only
gap is that the bare IH motive does not carry GP to discharge them. Durable:
`notes/Phase22a.md`.

### 1.3 What breaks if the motive is strengthened

Settled: the ripple is bounded and front-loaded (one `HasFullRankRealization` re-type
+ base-case GP conclusion); device feeds get *easier*, not broken; the one new burden
is the non-GP parallel-K₂ base. Durable: `notes/Phase22a.md`.

### 1.4 Recommendation

Decided: strengthen the motive, GP conditioned on `G.Simple`, via the **two-motive
split** (`HasGenericFullRankRealization` carried through simple cases + a forgetful
map to bare `HasFullRankRealization`) — the lower-ripple option touching no Phase-20
node. Durable: `HasGenericFullRankRealization`, `hasFullRankRealization_of_generic`;
`notes/Phase22a.md`.

### 1.5 Generic-motive recon — the route is a hybrid (2026-06-04)

Settled the N6-composer IH-shape gap as a hybrid (Route 2 *and* Route 1): N6-G1 makes
the producer generic directly (`hasGenericFullRankRealization_of_splice_ofNormals`,
GREEN, bypassing the device); N6-G2 makes the IH generic via a conditioned reduction.
Durable: `notes/Phase22a.md`.

### 1.6 N6-G2 re-recon — the generic-motive reduction, decomposed (2026-06-04)

Decided: condition the motive on `G.Simple`; cut into G2a (reduction skeleton) / G2b
(`map`/`rigidContract` simplicity) / G2c (wire into simple Case-I). All GREEN.
Durable: `notes/Phase22a.md`.

### 1.7 N6-G3 re-recon — the `Gc ≤ G` mismatch is Claim-6.4 transport (2026-06-05)

Settled: the `Gc ≤ G` mismatch dissolves at the graph level (contraction leg is
`G ＼ E(H)`, not the relabelled `rigidContract`) but relocates to the placement level
as genuinely-new KT Claim 6.4 transport. Cut into G3a/G3b/G3c. Durable:
`notes/Phase22a.md`.

### 1.8 G3c re-recon — body-set mismatch, NOT pure green-brick assembly (2026-06-05)

Found every Case-I coupling hardcodes each leg rigid on its *full* vertex set, but the
contraction leg is rigid only on `V∖V′∪{v∗}` — forced building body-set variants of
the splice/coupling bricks. Durable: `notes/Phase22a.md`; G3c-i producer bricks.

### 1.9 G3c-ii re-recon — route (a), PARTLY WRONG (corrected §1.12) (2026-06-05)

Decided to carry the body-set complement-isolation `hpin` as a hypothesis. The
`H`-half is honest but the contraction-leg `hpinc` is generically unsatisfiable,
making `case_I_realization` valid-but-vacuous. Durable: §1.12; `notes/Phase22a.md`.

### 1.10 G3c-iii re-recon — GP conjunct needs a body-set generic coupling, built (2026-06-05)

Landed the two body-set generic producer bricks; re-cut the residual assembly into
G3c-iii-a (parent-`ends` impedance) + G3c-iii-b (composer assembly), having found two
unsurfaced obstructions. Durable: `notes/Phase22a.md`.

### 1.11 G3c-iii-a re-recon — the parent-`ends` impedance dissolves (2026-06-05)

Settled: the producers need only an *edge-restricted* `hends`, constructible from `G`
alone (option (iii)) — not a layer-wide motive re-typing. Durable: `notes/Phase22a.md`.

### 1.12 G3c-iii-b correctness gap — `hpinc` is a FALSE equality (2026-06-05, coordinator verification)

Diagnosed: `hpinc` is a placement-independent combinatorial equality (not Claim 6.4),
generically false. Decided route (b)-corrected (an asymmetric coupling deleting
`hpinc`) — landed, then **superseded by §1.13's re-architect**. Durable: §1.13.

### 1.13 Second coordinator verification — the asymmetric fix ALSO undischargeable; re-architect (2026-06-05)

Found the §1.12 fix needs the false "GP ⟹ rigid"; root cause is Phase-21b's
common-seed motion-space splice glue vs KT's block-triangular rank-addition.
**Owner-directed: re-architect Case I to KT's block-triangular form.** Durable:
§1.14; `DESIGN.md` *Match the source's argument structure …*.

### 1.14 Block-triangular reframing — design, verified (2026-06-05)

Designed the reframe: KT eq. (6.3) rank-addition via the device's independent-row
counting; leaves one honest residual `hsc_proj_indep` (exterior-projected
surviving-row independence = KT Claim 6.4 eq. 6.5/6.9). Durable: §1.16;
`notes/Phase22b.md`.

### 1.15 Stage 3 — molecular 17–22 KT-divergence audit, clean (2026-06-05)

Audited phases 17–22 for sibling divergences: Case-I splice (§1.13) is the only one;
Cases II/III already use KT's block-triangular column split, corroborating the
reframe. Durable: `notes/Phase22b.md`, `notes/Phase21a.md`.

### 1.16 The Stage-4 residual was over-quantified; dischargeable as Qc-non-root (2026-06-05)

Corrected: `∀ q, GP(q) → …` needs the false "GP ⟹ max rank"; the dischargeable form
conditions on a surviving rank polynomial's Qc-non-root, reducing to KT eq. (6.9).
Meta-lesson promoted to `DESIGN.md`. Durable: `notes/Phase22b.md`.

### 1.17 N-22b-1 re-recon — the analytic core is `htransport` (2026-06-05)

Decided N-22b-1 carries the single-placement exterior-projected surviving-row
witness as explicit `htransport` (KT eq. 6.9); admits no green-brick reduction.
Softened by §1.18. Durable: §1.18; `notes/Phase22b.md`.

### 1.18 Validation of the `htransport` deferral + discharge plan (2026-06-05)

Validated the deferral but softened §1.17: a concrete 5-node cut (T1→T4) reusing the
genericity engine, T2b the analytic crux. Paused at the checkpoint. Durable: §1.19;
`notes/Phase22b.md`.

### 1.19 T2b math-first re-recon — WRONG, corrected by §1.20 (2026-06-05)

Claimed T2b dissolves (lower-semicontinuity already green) and the crux shrinks to
T2a. **Corrected by §1.20: the crux did not vanish, it moved to U3.** Durable: §1.20;
`notes/Phase22b.md`; cross-ref `DESIGN.md` *Recon at build fidelity*.

### 1.20 The U2 build surfaced the real crux — U3 is NOT plumbing (2026-06-05)

Found U3 needs a pin-a-body rank-preservation brick (genuine KT Claim 6.4): the
exterior projection drops the `r`-column. Split into U3a (bricked) + U3b (missing
infra). **Corrected by §1.21/§1.22.** Durable: §1.21; `notes/Phase22b.md`.

### 1.21 U3b recon — WRONG, corrected by §1.22 (2026-06-05)

Claimed U3b is one bounded brick via `finrank Z = D`. **Corrected by §1.22: false
for `sc ≠ α`** (it is `D·(|scᶜ|+1)`). Durable: §1.22; `notes/Phase22b.md`; cross-ref
`DESIGN.md` *a "rigid" framework's null-space dimension depends on rigid-on-what*.

### 1.22 U3b build-recon — corrected and BUILT (2026-06-05)

Corrected the layer and built it: the brick reduces to `Z ⊔ range(extProj V(H)) = ⊤`,
real content = the rigid-block pin-count `finrank(pinnedMotionsOn_F V(H)) =
D(|scᶜ|−|V(H)|+1)`. All U3b sub-bricks landed, axiom-clean. Durable:
`notes/Phase22b.md`.

### 1.23 U3a build-recon — NOT buildable as scoped, needs motive strengthening (2026-06-05)

Found the IH motive carries an *arbitrary* `ends` with no link-recording, so the
`endsᵐ`-swap transport fails (the same gap is already undischarged for the `H`-leg).
Lesson lifted to `DESIGN.md` *A realization motive must carry the selector
invariants its consumers read*. Durable: §1.24; `notes/Phase22b.md`.

### 1.24 Route-(i) scope verification — buildable, generic-motive only (2026-06-05)

Verified the link-recording strengthening buildable: scope is generic-motive-only,
every producer supplies link-recording for free, three risk items confirmed. Gave
the 5-commit sequence ending in the `lem:claim-6-4` flip + phase close. Durable:
`notes/Phase22b.md`.

---

### 1.25 Phase 22c opens — Case III at `d=3` (KT Lemma 6.10), first layer recon (2026-06-05)

22b closed (Claim 6.4 green). Phase 22c opens Case III / Track B (KT §6.4.1, ~12
pages), design-pass-first: the eq. (6.12) degenerate placement gives
`rank ≥ D(|V|−1)−1`, one short; the Claim-6.11/6.12 argument supplies the missing
row. Scope cut: 22c = Case III at `d=3` only. Durable: `notes/Phase22c.md`; four
open questions → §1.26.

### 1.26 Phase 22c, second pass — four questions + three-strata scope cut (2026-06-05)

Resolved: (Q1) one per-candidate row-op lemma, instantiated ×3; (Q2) `d=3`-first YES
(KT's own cut; general `d` → Phase 23); (Q3) Claim 6.11's bridge = Lemma 4.3(ii)+IH;
(Q4) Claim 6.12's "same `r`" is eq. (6.44). Partitioned Lemma 6.10 into three
strata, cut **22c = stratum 1** (eq.-(6.12) placement). Durable: `notes/Phase22c.md`.

### 1.27 Phase 22c, third pass — blueprint reconciliation (2026-06-05)

Found the live blueprint prose self-inconsistent (statements said nodes
"superseded" while proofs still routed through them). Reconciled to the eq.-(6.12)
row-side route; the calibration case behind the supersession gate. Durable:
`notes/Phase22c.md`; `blueprint/CLAUDE.md` *supersession gate*.

### 1.28 Phase 22c, fourth pass — signature-level verification of the stratum-1 cut (2026-06-05)

Confirmed the one new brick composes cleanly against five green bricks (no
mismatch); `panelRow (ofNormals G ends q)` reads only `ends`+`q`, not `G`. Count
`(D−1)+D(|V|−2)=D(|V|−1)−1` closes — a lower-bound brick. Durable: `notes/Phase22c.md`.

### 1.29 Phase 22c, fifth pass — single-seed coupling + placement geometry (2026-06-05)

(A) single-seed coupling sound (IH rigidity untouched by `v`'s update); (B)
placement `n_a+t·n_b`, `t≠0`, reproduces the `ab`-row while keeping `va`
nondegenerate; (C) sub-lemma bounded, landed as
`linearIndependent_panelRow_comp_single_of_edge`. PLAN CLEAR. Durable:
`notes/Phase22c.md`.

### 1.30 Phase 22d, footnote-6 kernel recon (2026-06-06)

Confirmed the matroid↔row link + redundancy-from-count are green, but refuted
"eq. (6.22) re-exposes from the device" — the motive is not rank-poly non-root-ness
and the project had zero `AlgebraicIndependent` machinery. Named the new content: a
non-root-from-algebraic-independence brick. Durable: `notes/Phase22d.md`;
`notes/AlgebraicIndependence.md`.

### 1.31 Phase 22d, kernel-route decision + alg-independence tracker (2026-06-06)

**User decision: build the algebraic-independence route DIRECTLY to green** (KT's
actual argument), not carry-as-hypothesis. The product-route shortcut deferred,
tracked in the standing note `notes/AlgebraicIndependence.md`. Durable:
`notes/Phase22d.md` *Kernel-route decision*.

### 1.32 Phase 22d, kernel sub-phase (ii) opening recon — SPLITS (2026-06-06)

Found (ii) is not one leaf: **(ii-a)** the seed-genericity motive conjunct
[plumbing] + **(ii-b)** a rationality bridge [NEW — the device's `Q` is ℝ-typed, not
manifestly rational; needs a `ℚ→ℝ` descent for the rank polynomial; zero such
scaffolding in tree]. Durable: `notes/Phase22d.md`; `notes/AlgebraicIndependence.md`
row #105.

### 1.33 The `d=3`-assembly opening recon + the Phase-23 general-`d` reuse map (2026-06-07)

**(A)/(B) — verdict landed, canonical home `notes/Phase22g.md`.** Re-scoped to one
real gap (the `d=3` `hsplit` producer); **(B.1)** `lem:cycle-realization` (KT Lemma
5.4) is a narrative, not Lean-load-bearing, dependency; **(B.2)** add a small `d=3`-
instance `theorem_55` node. Full verdict + build spine: `notes/Phase22g.md`
*Red-node consistency gate*.

**(C) KT §6.4.2 (Lemma 6.13) reuse map.** Table moved to
`notes/MolecularConjecture.md` *Reuse map* — headline: Claim 6.11 + Lemma 2.1 reuse
**verbatim, GREEN**; the genericity device/Cases I/II spine is `k`-free; the
`⋀²ℝ⁴` duality is `d=3`-only, **replaced** by `⋀^{d−1}ℝ^{d+1}` at general `d`; the
candidate/chain bookkeeping (eqs. 6.46–6.64) is **NEW** but mechanical; Lemma 5.4
(cycle base) is the deferred risk.

**(D) Grassmann–Cayley / exterior-duality API — build it LAZILY in Phase 23.** No
general Hodge-star API needed (KT only uses the top-power-is-1-dimensional fact);
the general route's infra is *already partly landed* (the "unused" 22f
`exteriorPower.map`-range facts generalize; the bespoke `⋀²ℝ⁴` count does not).
Alg-independence machinery for the general-position points already exists (22d).

**(E) Recommended sequence.** Open the `d=3` assembly sub-phase on a build-free
red-node consistency recon ((B.1)–(B.2)); then Phase 23 (general `d`) reusing Claim
6.11/Lemma 2.1 verbatim, generalizing the candidate chain, building the
`⋀^{d−1}` duality via the top-power route, applying the existing alg-independence
machinery, using the `d=3` assembly as template.

---
### 1.34 The `d=3` `hsplit` producer core — cracked into named leaves (2026-06-07)

Decomposed the `hsplit` producer into named leaves (L0 skeleton + L1–L5), reusing
green row-transport infra (N7b-2) verbatim and isolating one defeq trap to L3.
**Superseded by §1.35**: the L3/L5-pack device-feed route (`panelRow`-shaped) does
not work — KT's `+1` candidate row is provably not a single `panelRow`. Durable:
§1.35; `notes/Phase22g.md`.

### 1.35 The `d=3` L-wire — corrected candidate-row placement + device feed (2026-06-07)

Corrected the device feed: the candidate row is a genuine rigidity-row-span member
(a combination of `e_b`-panelRows), not a single `panelRow`; fixed via a NEW
fixed-framework device-feed variant `hasFullRankRealization_of_independent_rigidityRow`
(built on `exists_good_realization_const`, not `_ofParam` — no genericity, no
row-swap, no panelRow re-shaping). Leaves C1 (fixed-framework feed) → C2
(single-candidate brick) → C3 (rewire L0) → C4/C5 (`theorem_55` instance + flips).
This is the corrected device feed §1.39/§1.41 etc. build on. Durable:
`notes/Phase22g.md`.

### 1.36 The `hduality` six-join modeling subtlety (2026-06-08)

Found `case_III_claim612`'s three-fixed-`Cᵢ` conclusion mis-modeled: KT's Claim 6.12
quantifies over *every* panel line (eq. 6.45), not three fixed extensors. Restated
to the per-panel-line model (route (a)); conclusion unchanged. **Superseded on the
antecedent side by §1.37/§1.39** (this pass fixed only the conclusion). Durable:
§1.39.

### 1.37 The `hann` discharge — verdict (B), SUPERSEDED by §1.39 (2026-06-09)

Found `hduality`'s *antecedent* (still three fixed scalars) has the same mis-shaping
§1.36 fixed on the conclusion; three vectors span ≤3 of `⋀²ℝ⁴`'s 6 dims, so it is
undischargeable. Proposed carrying `hann` (the union premise) directly. **Superseded
by §1.39**: the cleaner fix drops the premise entirely. Durable: §1.39.

### 1.38 The `hann`-discharge re-adjudication, SUPERSEDED by §1.39 (2026-06-09)

Confirmed §1.37's diagnosis, refuted the "three-fixed-suffices" escape (KT's lines
are freely chosen, not graph-fixed), but overstated the producer's remaining work as
"only a quantifier" — it is a genuine re-parameterization. **Superseded by §1.39**:
the coordinator's existential-conclusion fix is cleaner still. Durable: §1.39.

### 1.39 The definitive `d=3` Case-III crux architecture (2026-06-09)

**Live architecture (supersedes §1.36–§1.38).** Restated `case_III_claim612` to the
**existential conclusion, no `hduality`/`hann` premise at all**: `∃ join` (of the six
joins of 4 affinely-independent points) `r ≠ 0` at that join — a 5-line contrapositive
via `span_omitTwoExtensor_eq_top` + `eq_zero_of_annihilates_span_top` (verified to
close). This makes the C5c six-join assembly + its two bricks **obsolete on the live
route** (kept as reusable lemmas; may re-enter at Phase-23 general-`d`). The producer
(`case_III_hsplit_producer`) must build the candidate placement **at the witness
join's line** — a line-indexed re-parameterization, the genuine remaining work,
unchanged in difficulty from §1.38. Leaf sequence: existential restate (done) → the
line-indexed candidate placement → wire the producer → `theorem_55` `d=3` instance →
blueprint flips. Durable: `case_III_claim612` (RigidityMatrix.lean);
`notes/Phase22g.md`.

### 1.40 The CaseI.lean producer-core recon — verdict (B) (2026-06-09)

Confirmed the line-indexed candidate placement is constructible for an arbitrary
witness join: the candidate's `va`-line is fixed by the IH seed (not the shear), and
the non-degeneracy needed (nonparallel panels, affinely-independent points, a
transversal second normal per opposite join) is supplied by the producer's own
N3a-style construction, not a fragile hypothesis. Two genuine residuals flagged:
**(R1)** reconciling the abstract N3a witness-points with the real candidate-panel
normals; **(R2)** the split-leg `ab`-transversality (needs the GP motive — resolved
§1.41). Durable: §1.41, §1.42; `notes/Phase22g.md`.

### 1.41 The R2 producer-signature verdict — (B) (2026-06-09)

Settled R2: the `hsplit` producer must consume the **GP** `_hsplit` (`hsplitGP`
branch) to get the `ab`-hinge transversality `hgab` — the genericity the producer
reads off its GP split-leg; a bare rigid realization does not force it (KT's own
"nonparallel, if simple" rests on the same GP data). The green Case-I precedent
(`case_I_realization`/`hcontractGP`) does exactly this. **(5) The route**: restate
the producer to `theorem_55_generic.hsplitGP`, pulling `q`+`hgab` from the GP
conjunct after discharging the `(G.splitOff …).Simple` antecedent — a new bounded
sibling of Case I's `rigidContract_simple` (**R3**, resolved §1.42/§1.43). Leaf-4
ripple: instantiate `theorem_55_generic`, project the bare `.2` conjunct (absorbed
by the existing two-motive skeleton). Durable: §1.42;
`CombinatorialRigidity/Molecular/AlgebraicInduction/CaseIII/Arms.lean`.

### 1.42 Two residuals settled: R1-affine (A) dissolves; R3 (A) clean mirror (2026-06-09)

**R1-affine dissolves**: the affine de-homogenization §1.40 flagged is never needed
— Lemma 2.1's proof and the seed-from-line bridge both use only `LinearIndependent`
of the homogeneous vectors, not affineness; restate the two consumers to bare
`LinearIndependent ℝ pbar` and feed the homogeneous core directly — no
de-homogenization, no at-infinity case, no genericity. **R3 is the clean bounded
triangle mirror**: KT Lemma 6.7(ii)'s proof (a parallel `ab`-edge in `G_v^{ab}`
forces the triangle `{va,vb,ab}` as a proper rigid subgraph, contradicting
`hnoRigid`) needs NO 2-edge-connectivity, only `G.Simple`+`hnoRigid`+the split data
— a new `Operations.lean` leaf, sibling of `rigidContract_simple`. Combined, the
Leaf-3 producer is genuinely buildable. Durable:
`CombinatorialRigidity/Molecular/Extensor.lean`,
`CombinatorialRigidity/Molecular/RigidityMatrix/Claim612.lean`.

### 1.43 The R3-triangle-brick recon (2026-06-09)

Pinned the `htri` sub-brick's proof route: at `d=3` the triangle is *exactly*
`(D,D)`-tight (`3(D−1)=2D` at `D=3`), so no circuit exists inside it and the
existing `circuit_induces_isRigidSubgraph` route does not apply. The `n`-uniform
route is a direct full-rank computation via an explicit `D`-spanning-tree packing
on `(K₃)̃` (Tutte–Nash-Williams, already in tree for the boundary regime) —
buildable, a genuine count (~1–2 commits), not a one-liner. Durable:
`notes/Phase22g.md`.

### 1.44 Three Leaf-3 sub-obligations adjudicated (2026-06-09)

Re-examined the §1.41/§1.42 recons against the actual reduction skeleton and found
two of three sub-obligations are **genuine holes**, not bounded residuals: **GAP 1
(C)** — `|V(G)|=3` IS reachable on the `hsplit` branch (the triangle has no proper
rigid subgraph), where R3's `4≤|V|` proper-ness guard is unmet; **GAP 2 (C)** — the
eq.-(6.12) sheared candidate seed is algebraically dependent over ℚ *by
construction*, so it can never carry the GP motive's `AlgebraicIndependent ℚ`
conjunct the way `case_I_realization` does; **GAP 3 (A)** — bounded (the bad
shear-parameter `t` set is a single value). Lesson: recon the target's proof route
end-to-end against the *consuming skeleton*, not just its statement. **GAP 1/2 both
later resolved/refined — see §1.45–§1.48.** Durable: `notes/Phase22g.md`.

### 1.45 GAP 2 resolution — verdict (B-derive) (2026-06-09)

Overturned §1.44's "GAP 2 is research-shaped": the producer need not conclude the
generic motive *at the degenerate seed* — it builds the degenerate candidate to
**bare** `HasFullRankRealization` first, then a **bounded new upgrade leaf**
(reusing `exists_rankPolynomial_of_rigidOn`'s rank-polynomial machinery)
re-realizes it generically at an algebraically-independent seed — exactly KT's own
argument (Lemma 6.8: build a degenerate witness, invoke Lemma 5.2's "convert to
nonparallel without decreasing rank"). Confirmed L-independent (the witness line is
consumed before the upgrade, discarded after). Durable: `notes/Phase22g.md`.

### 1.46 GAP 1 "dissolved" — RETRACTED by §1.47 (2026-06-09)

Claimed the producer never needs split-simplicity (takes the bare `.2` IH conjunct
directly), so GAP 1 dissolves, and that §1.44's proposed `|V|=3` patch is false (the
triangle's `splitOff` is a genuine parallel pair, not a simple single edge — this
half **stands**). **Finding (1) is retracted by §1.47**: it orphans `hgab`, which
the candidate placement needs and only the `.1` (GP) conjunct supplies. Durable:
§1.47.

### 1.47 Coordinator cross-check — §1.46 is UNSOUND (2026-06-09)

Corrected: `.1` (the GP conjunct) IS on the live route (needed for `hgab`), not
unused. Corrected picture: `|V(G)|≥4` buildable via `.1`+R3; **`|V(G)|=3` is a
GENUINE HOLE** — the triangle's split is the non-simple `K₂` where GP itself fails,
so `hgab` is unavailable by either route, and KT handles `|V|=3` separately (a
direct triangle realization, Lemma 5.4/6.7(i)) which the project's reduction routes
into `hsplit` instead. Process lesson (promoted): a recon that re-routes to
dissolve one gap must re-verify every other carried obligation still closes under
the new route. Durable: §1.48; `CLAUDE.md` *Referencing prior work* neighbours.

### 1.48 The §1.47-commissioned recon (2026-06-09)

**(1) The `|V|=3` triangle base case** — verdict: NEW bounded work (~3–4 commits,
T1–T4: the triangle's third edge + vertex pin, a three-body rigidity brick, an
explicit independent-normals seed, the assembly), on the *critical path* of the
whole `hsplit` recursion (every split chain passes through it). **(2) The `|V|≥4`
route** confirms §1.47's `.1`-in-the-loop wiring, but tracing the six-join
*dispatch* surfaces **GAP 4**: KT's `M₃` third-panel candidate (a *second* split at
an adjacent degree-2 pair, eqs. 6.41–6.44) is absent from the leaf inventory and
inexpressible in the current `hsplit`/`hsplitGP` branch interface (which hands the
producer only ONE fixed split). Five new leaves named (G4a chain-dichotomy, G4b
branch-interface decision, G4c ρ-relabel transport, G4d the `a`-column bookkeeping,
G4e the dispatch). Durable: `notes/Phase22g.md`.

### 1.49 The GAP-4 interface design pass (2026-06-09)

**G4b verdict (β)**: hand the `hsplit`/`hsplitGP` branch the **full conditioned IH**
(mirroring `hcontract`'s shape) rather than re-pointing the reduction's degree-2
selection (α) — KT-faithful (Lemma 6.10 itself invokes the IH at a second,
non-split object) and minimal-ripple (the closed Phase-20 reduction + bare
`theorem_55` stay untouched; only the unconsumed `theorem_55_generic` restates).
G4a–G4e scoped to leaves with pinned signatures; the producer **chooses its own
adjacent degree-2 pair** via the chain dichotomy at (1). **PLUS GAP 5,
machine-verified**: `IsProperRigidSubgraph` admits single-vertex subgraphs, so
`hnoRigid` is *unsatisfiable* whenever `2≤|V(G)|` and the reduction's rigid/no-rigid
dichotomy is degenerate as stated — repair the predicate (add `2 ≤ |V(H)|`) before
any G4 build; bounded, 1–2 commits, and KT's own text has the same surface
degeneracy (silently excludes trivial subgraphs). Durable: `notes/Phase22g.md`;
`blueprint/src/chapter/deficiency.tex` `def:rigid-subgraph`.

---

### 1.50 The `hcand`-discharge recon — the sheared M-arm route dissolves via a KT-Lemma-5.2 rank transfer; GAP 6 surfaced (2026-06-10)

**(a)** BUILDABLE — restate `exists_line_data_of_homogeneousIncidence` /
`exists_complementIso_ne_zero_of_homogeneousIncidence` (RigidityMatrix.lean) in place at the
discriminating level: both already return a real normal (`n u`, per-join `u` case-checked over
the six `fin_cases` branches); no consumer outside RigidityMatrix.lean. Dispatch `u = 0/1/2 ↦
M₁/M₂/M₃`. Landed as W1 (`f6dbae9`).

**(b)** `h618` (eq. (6.18), the split's full rank at the IH seed) is a micro-leaf (landed W2,
`finrank_span_rigidityRows_of_rigidOn`). `h622` (eq. (6.22)) reduces to one open input: **GAP 6**
— the eq.-(6.22) rank lower bound at the nested-IH `k'`-dof `G_v` (KT's IH (6.1) at a `k' > 0`
graph), unsuppliable from the project's then-0-dof-only induction motive (three dead-end routes
verified: the deterministic hub bound runs the wrong way; augmenting `G_v` to 0-dof loses too
much; the row-level increment bound is false). **Adjudicated (user, 2026-06-10): carry-and-defer**
— ride `h622lb` as an explicit hypothesis through W5→W10, discharged later by the all-`k` motive
restructure (§1.56); the alternative (strengthen the motive now) is phase-sized. Landed as the W5
packaging (`fd26a87`).

**(c)** The §1.49(5) sheared-placement route as scoped is undischargeable (the sheared seed's
transported `(vb)ⱼ`-rows are not rows of the sheared candidate at `t ≠ 0`) — and the `hold`-shaped
(v-vanishing) OLD block of `case_III_{full_family,realization}_of_line` caps one short of KT's
(6.29) count at any non-degenerate line, because **KT's (6.29) bottom block is NOT v-vanishing; it
is restriction-independent** (the `(vb)ⱼ`-rows restricted to `V ∖ {v}` reproduce the split's rows
after the column op) — DISSOLVES via KT Lemma 5.2 (pp. 668–669, "each minor of `R(G,p_t)` is
continuous in `t`") made one-variable-polynomial: certify the full KT-(6.29) row count at the
**`t = 0`** hinge-level family `F₀` (every membership holds by construction there), then transfer
linear independence along the shear for good `t ≠ 0` (entrywise polynomial, nonzero at 0 ⟹ nonzero
a.e.). New graph-free leaves: **A0** (the restriction-independent — not v-vanishing — bottom
block-triangular augment, landed W4 `20c0ccb`), **B** (the one-variable rank-transfer engine,
landed W3 `9a5108b`), **A1/A2** (the `F₀` certification + arm closer — refined into seven leaves at
§1.51). Buildable modulo GAP 6; re-verified against KT (6.16)/(6.23)/(6.29).

**(d)–(e)** M₂, M₃ are role-swapped / relabeled instantiations of the M₁ chain (same `F₀`/`g`/
A0–A2 pattern; M₃ additionally threads `ofNormals_relabel` (G4c-ii) + `candidateRow_ac_eq_neg`).
No new leaves beyond wiring; buildable after M₁, modulo GAP 6 (M₃'s design settled at §1.52 —
`ofNormals_relabel` itself later drops off the live route there).

**(f)** Build order W1–W10 (superseding §1.49(6) item 5): W1 discriminator, W2 `h618`, W3 leaf B,
W4 leaf A0, W5 redundancy packaging (GAP-6 carry), W6/W7 the M₁ certification + closer, W8 M₂,
W9 M₃, W10 the dispatch + discharge assembly. **Superseded by §1.51**: W6/W7's single slot is
replaced by seven exact-signature leaves W6a–W6f + W7 once a flaw in the `t = 0` sketch surfaced
(the certify-then-rebase correction, §1.51(a)). All ten items landed 2026-06-10/11 (Phase 22h).

**GAP 6 adjudicated (user, 2026-06-10): (ii) carry-and-defer** — see (b).

---

### 1.51 The W6-concrete decomposition — seven exact-signature leaves W6a–W6f + W7 replace the single W6/W7 slot; the §1.50(c) sketch corrected to certify-then-rebase (2026-06-11)

**(a)** Refines §1.50(c): the certified `t = 0` mixed (6.29) family is NOT itself the transfer
family `g` (its candidate row and transported `(vb)ⱼ`-rows are not sheared-candidate rows at
`t ≠ 0` — the same obstruction §1.50(c) diagnosed for the `_of_line` OLD contract). Corrected
route = **certify-then-rebase**: (1) certify the mixed (6.29) family independent at `F₀` (KT
p. 684's *rank* reading of (6.29), not a distinguished row family); (2) **rebase** — every member
lies in `span F₀.rigidityRows` (the candidate via the eq.-(6.27) collapse `hingeRow v a ρ =
hingeRow v b ρ − hingeRow a b ρ`), giving `D(|V(G)|−1) ≤ finrank(span F₀.rigidityRows)`, from
which a **literal `F₀.panelRow` family** of that size is re-extracted (each slot genuinely
polynomial in the shear parameter); (3) **transfer** the re-extracted family along the
`t`-family of frameworks via leaf B. Everything else in §1.50(c) stands (F₀ hinge-primary,
`t = 0` memberships by construction, the witness gate consumed only at `t = 0`).

**(b)** W6a — `PanelHingeFramework.caseIIICandidate` (CaseI.lean), the role-parametric `t`-family
(KT's `p₁` at shear `t`; M₁: `e_c=e_a,e_r=e_b`; M₂ swaps `a↔b`; M₃ passes the relabeled seed
`qρ`), plus its affinity/evaluation lemmas and the `panelSupportExtensor`/`annihRow` first-slot
linearity + restriction-transport bricks it needs (the (6.26)–(6.28) membership-by-construction,
in functional form). Landed.

**(c)** W6b — `exists_candidateRow_bottomRows_of_rigidOn` (CaseI.lean): from ONE invocation of
W5's redundancy data (KT p. 686: the same `λ_{(ab)j}`/`i^*` feed both (6.29) and (6.30)), packages
the candidate functional `ρ` (`r̂ = hingeRow a b ρ`) plus the chosen `D(m−1)` bottom rows of
`R(G_v^{ab} ∖ (ab)i^*, q)` (KT eq. (6.23)). **GAP-6 entry point**: `h622lb` (§1.50(b)'s carried
inequality) enters here, carried onward by W6b (W5's sole caller) to W10; W6c–W6f/W7 consume only
W6b's outputs and are GAP-6-clean. Landed.

**(d)** W6c — `case_III_full_family_restriction` (CaseI.lean): the restriction-bottom sibling of
`case_III_full_family_of_line` (same NEW-block construction, but the bottom block enters via W4's
restriction-independence contract); independently buildable off only W4-era + W6-core infra (no
W6a/W6b dependency). Landed.

**(e)** W6d — `case_III_rank_certification` (CaseI.lean; the moderate-§38 leaf, mitigated by the
`hrow_mem` explicit-link-witness idiom): concludes the (6.29) count at `F₀` as the rank lower
bound `D(|V(G)|−1) ≤ finrank(span F₀.rigidityRows)`, via bottom-row transport (two restriction
bricks) + W6c + membership-by-collapse. Landed.

**(f)** W6e — `exists_independent_panelRow_subfamily_of_le_finrank` (GenericityDevice.lean):
generalizes `_of_rigidOn_linking` to consume a bare rank bound instead of rigidity (`F₀` is not
yet known rigid at this point); `_of_rigidOn_linking` refactors to a 3-line corollary via W2 in
the same commit. Independently buildable. Landed.

**(g)** W6f — `caseIIICandidate_exists_good_shear` (CaseI.lean): leaf B (the one-variable
rank-transfer engine) specialized to `caseIIICandidate` — KT Lemma 5.2's continuity claim in
one-variable-polynomial form. Landed.

**(h)** W7 — `case_III_arm_realization` (CaseI.lean; THE §38-exposed leaf, mitigations named): the
role-parametric M₁-arm closer, assembling W6d→W6e→W6f→membership-at-good-`t`→GAP-2 into
`HasGenericFullRankRealization`. Supersedes the §1.50(f) "W6/W7 M₁ closer" slot; W8 (M₂) becomes a
pure instantiation of it (see (i)). Landed.

**(i)** Supersession + M₂/M₃/W10 refined roles. §1.50(f)'s "W6 — A1, then W7 — A2" is superseded
by W6a–W6f + W7 (A1 ↦ W6c+W6d, A2 ↦ W6e+W6f+W7). **W8 (M₂)** is a pure instantiation of W7 at
swapped roles `(a,b,e_a,e_b,n') := (b,a,e_b,e_a,n'')`, `ρ' := −ρ` (`hingeRow_swap`, a
Lean-orientation artifact — KT p. 681 "`r'` is indeed equal to `r`"). **W9 (M₃)** stays scoped as
§1.50(e) (G4c/G4d wiring + `candidateRow_ac_eq_neg`), targeting W7 at the relabeled `a`-split;
exact shapes deferred to the W9 design moment (§1.52). **W10** (dispatch + discharge) unchanged in
role: unpack `hsplitGP`, override the selector at the two re-inserted hinges (case-split on
recorded order — the swap-ambiguity finding corrected at §1.53(a)1), derive `hgab`/triple-LI from
GP, invoke W6b (GAP-6 on W10's signature), dispatch `match u with 0↦W7 | 1↦W8 | 2↦W9`.

**(j)** Build order (replaces §1.50(f) item 6): W6a → W6c ∥ W6e → W6b → W6f → W6d → W7 → W8 → W9
→ W10 → Leaf 4/5, closing green-modulo-GAP-6. All seven new leaves landed 2026-06-11 (Phase 22h).

---

### 1.52 The W9 design moment — W9 IS a W7-instantiation at `Gv := G − a`; the 365740b "not-a-W7-instantiation" finding attacked a config never proposed (2026-06-11)

**(a)** The adjudication: **W9 IS a W7-instantiation at `Gv := G − a` with the relabeled seed
`qρ`; Route A wins, three leaves.** The 365740b hand-off finding said W7's `hleG` forces `Gv ≤ G`,
while the M₃ rigidity certificate lives on the relabeled `a`-split `∉` subgraphs of `G` — true,
but §1.51(i)'s `Gv`-slot is "the relabeled split minus its short-circuit edge", i.e. `G.
removeVertex a`, which IS a subgraph of `G`. KT answers where the M₃ candidate/bottom data at
`(G − a, qρ)` comes from at eqs. (6.35)–(6.41) (pp. 687–689): KT never realizes the a-split — the
rank argument runs bodily against `R(G, p₃)`, whose (6.36) column op + (6.38)–(6.39) row
correspondence identify the bottom block of (6.41) with **the same v-split matrix**
`R(G_v^{ab} ∖ (ab)i^*, q)` as M₁/M₂'s (6.29)/(6.30) — same `λ`s, same `i^*`. **No a-split rank
certification, hence no second GAP-6.** The M₃ data transports POINTWISE from the ONE v-split W6b
invocation; the re-derivation route (Route B: fresh W6b at the a-split, or re-deriving the whole
certify-then-rebase chain against a-split rows) is strictly dominated — it duplicates ≈600 landed
lines for zero reuse, still hits the same `e₁`-elimination Route A needs anyway, and (under the
fresh-W6b reading) creates a **second undischargeable GAP-6 carry** (the §1.50(b) dead end applies
verbatim at `a`). Two new transport leaves W9a/W9b + the closer W9c; the relabel-SPAN bridge
(`mem_span_rigidityRows_ofNormals_relabel`) and the G4c-ii/G4d-ii suite drop off the live route.

**(b)** W9a — `funLeft_dualMap_sub_acolumn_mem_span_rigidityRows` (CaseI.lean, beside G4d-i): the
span-induction transport core, transporting a v-split-row-span member across the vertex relabel
with the `e_c`-content stripped (subtracting the `a`-column hinge row). Landed.

**(c)** W9b — `case_III_bottom_relabel` (CaseI.lean, after W9a; §38 exposure mild, mitigated): the
per-member conversion of one W6b bottom-family member from the v-split tag shape to the
W7-at-M₃-roles tag shape (three cases: the `(ab)`-block tag, the `Gv`-row `a`-incident tag, the
off-case). Landed.

**(d)** W9c — `case_III_arm_realization_M3` (CaseI.lean, after W9b; §38 exposure mild — the trap
lives inside W7): the W8-pattern instantiation commit, heavier conversions delegated to
G4d-i/W9a/W9b, consuming the **SAME** v-split W6b (`ρ`, `w`) package M₁/M₂ use (KT p. 686: one
redundancy computation feeds all three arms). Landed — all three M-arms now closed.

**(e)** Consumption/supersession ledger. **Live route** consumes W7, W6b's outputs, G4d-i,
`hingeRow_funLeft_dualMap`, `hingeRow_swap`, `panelSupportExtensor_swap`, `mem_hingeRowBlock_iff`,
the `removeVertex` API. **Landed but OFF the live route** (stay as green blueprint-pinned nodes
documenting KT (6.31)/(6.44) as stated fact — no `\uses`-route may claim the W9 chain routes
through them): `mem_span_rigidityRows_ofNormals_relabel`, `rigidityRows_ofNormals_relabel`,
`ofNormals_relabel`, `hasGenericFullRankRealization_of_splitOff_relabel`, G4d-ii
(`hingeRow_acolumn_mem_span_rigidityRows`), `candidateRow_ac_eq_neg`. **W10 boundary pre-brick**
(flagged, designed at §1.53): M₁/M₂'s W7 feed consumes `hρGv`/`hwmem` at the *overridden* selector
while W6b emits them at the IH selector — one row-set congruence lemma discharges it (W9 itself
needs no such lemma).

**(f)** Build order (refines §1.51(j)'s W9 slot): W9a (leftmost, only landed inputs) → W9b → W9c
→ W10 (+ the ends-congruence pre-brick of (e)) → Leaf 4/5, closing green-modulo-GAP-6. All landed
2026-06-11 (Phase 22h).

---

### 1.53 The W10 design-settle pass — exact signature pinned (`case_III_candidate_dispatch` + the ends-congruence pre-brick), plus three §1.51(i) corrections at the signature level (2026-06-11)

**(a)** Three §1.51(i) corrections (each would have blocked or mis-routed the builder). **(1)** The
recorded-order case split must **not** rename `(a, b)`: the chain roles are asymmetric (the
discriminator's `u`-dispatch is pinned to chain order `![n_a, n_b, n_c]`), so the fix is a
one-time sign/swap **normalization** of the W6b outputs to chain order (`ρ̂ := ±ρ`, the landed W8
conversion pattern applied once at the W6b boundary, before the discriminator) rather than
renaming per recorded order. **(2)** The GAP-6 carry cannot enter W10 at a fixed seed — the seed
is existentially bound inside `hsplitGP` — so `h622lb` enters **quantified** over `(ends, q)` and
conditioned on the IH-suppliable antecedents (link-recording, seed general position,
ℚ-algebraic-independence); the same quantified shape rides up to Leaf 4's wiring. **(3)** The M₃
branch needs a **third** selector override (at `e_c`, not just the two re-inserted hinges) — per
arm selectors differ, and `hebc` (needed for the third update) is derived from link uniqueness,
not carried by `hcand`.

**(b)** W10a — `rigidityRows_ofNormals_congr_ends` (CaseI.lean; independently buildable): the
ends-congruence pre-brick, scoped tighter than §1.52(e) flagged — only `hρGv`/`hwmem` (W6b outputs
stated at the IH selector, consumed at the overridden one) need it; `hends_Gv`/`hne_Gv` discharge
directly, and W9c needs no congruence at all. Selectors agreeing on links give equal
`rigidityRows` sets (the row set is `ends`-free; `ends` enters only through `supportExtensor`).
Landed.

**(c)–(d)** W10b — `case_III_candidate_dispatch` (CaseI.lean; §38 exposure moderate, mitigated):
matches `hcand`'s parameter shape plus `hsimple` plus the quantified GAP-6 carry; concludes the
generic motive. Proof route: unpack `hsplitGP` (the `hQeq` idiom) → inline graph facts → ONE W6b
invocation at `(Gab, Gv, Q.ends, q, e₀)` (the single GAP-6 consumption site) → normalize per (a)1
→ run the discriminator (`exists_homogeneousIncidence_of_normals` +
`exists_complementIso_ne_zero_of_homogeneousIncidence`) → `fin_cases u` and dispatch each arm
(`u=0↦W7`, `u=1↦W8`, `u=2↦W9c`) with per-arm selector overrides per (a)3. Landed.

**(e)** Leaf cut: **W10a** (the pre-brick, independently buildable) / **W10b** (the dispatch
lemma — no sub-leaf independently meaningful; per-arm feeds are each a few tactics given (d)). No
`sorry` anywhere; the only carried hypothesis is the quantified `h622lb`. §38 mitigations named
per proof step (the `hQeq` idiom, eval-lemma-only rewrites, named `set`s before `refine`, the
Row-family-argument `clear_value` idiom).

**(f)** Build order (refines §1.51(j)/§1.52(f)'s W10 slot): W10a → W10b → Leaf 4 (`theorem_55_
generic (n:=2)(k:=2)`, gaining the fully-quantified GAP-6 hypothesis) → Leaf 5 → phase close
green-modulo-GAP-6. Landed 2026-06-11 (Phase 22h).

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

---

### 1.68 The Phase-22j design — the shared span-transport placement abstraction (the Case-II/III/Lemma-6.8 analogue of the landed Case-I splice brick): a recon-verified **TWO-brick family**, not one — **Brick A** `le_finrank_span_rigidityRows_of_pinned_placement` (NEW, span-level rank, what L6b + 22k's Case III consume) + **Brick B** `case_III_old_new_blocks` (the EXISTING literal-`panelRow` device-feed shape, kept); Case I stays on its splice brick + coupler (contraction = `extProj`-projected-column geometry vs split = `single v` pin-a-body geometry — KT's own Lemma 6.2 vs 6.8 split); common cause of the L6b ≈1010-line inlining = the placement bricks key their conclusion on *literal* `G.rigidityRows` membership (forcing `Gv ≤ G`), but every real reduction graph (collapse / `splitOff` / relabel) lands rows only in `span(G.rigidityRows)`; verified read-only against the landed signatures (2026-06-14)

> **Read-only Plan-agent recon, verified by the coordinator against the landed Lean signatures.**
> Motivated by closing 22i: the L6b producer `case_II_realization_all_k` inlined a ≈1010-line
> eq.-(6.12) placement (the L6 episode, model-experiment row 118) because no shared brick fit the
> split-off `Gab = G.splitOff v a b e₀ ⋬ G`. The recon found the missing abstraction; the
> coordinator then verified each load-bearing claim against the source (the cited `file:line`s below).

**(a) The common cause (verified).** The placement bricks `case_II_placement_eq612` (CaseI.lean:3520,
rigid) and the now-dead `case_II_placement_eq612_kdof` (:3735, "L6a") both take `hGv : Gv ≤ G` and
conclude a *literal* independent subfamily of `G.rigidityRows` (count baked into the `∃ s`). `hGv` is
used in exactly one place — the OLD-block membership step `Graph.IsSubgraph.isLink_iff hGv` (:3705,
:3893). But every real reduction graph is **non-subgraph**: Case I's `rigidContract` (collapse), L6b's
`splitOff` (adds `e₀ = ab ∉ E(G)`), Case III's `removeVertex`+relabel. So the OLD rows land only in
`span(G.rigidityRows)`, and the literal brick fits no caller — each producer re-derives the placement
(inline for L6b; via case-specific bricks for Case III). The project already built the *correct* shape
for the Case-I problem — `le_finrank_span_rigidityRows_of_splice` (RigidityMatrix.lean:3213): span-level,
framework-agnostic, parametrized by an interface (`hFH_le`/`hFc_surv_le`/`hInj`) the caller discharges,
no subgraph hypothesis. The Case-II/III/Lemma-6.8 family never got the analogue.

**(b) The TWO-brick verdict (the recon's correction to a "one brick" first hypothesis; verified).**
The placement step lives in two genuinely different *conclusion shapes* that cannot be one brick:
- **(A) span-rank** — "`N ≤ finrank(span G.rigidityRows)`". This is L6b's `hN_FG` (:4513) / `hrank_lb`
  (:4708), and Case III's *rank* path `case_III_rank_certification` (:6261), whose interface is already
  span-transport (`hρGv : hingeRow a b ρ ∈ span(Gv.rigidityRows)` :6275 + the `hwmem` disjunction
  :6280–6283) and which does **not** consume `case_III_old_new_blocks`. **This is what L6b and 22k's
  Case III need.**
- **(B) literal device-feed** — an independent family of *literal* `G.panelRow`s of a given size,
  consumed by the genericity device `hasFullRankRealization_of_independent_panelRow_index`
  (GenericityDevice.lean:355), which **requires** literal panel rows (CaseI.lean:2997 confirms span
  members do not qualify). This is `case_III_old_new_blocks` (:5571).

(A) cannot return literal `G`-rows (the OLD rows are not `G`-rows after collapse/splitOff); (B) cannot
be span-transport (its consumer needs literal rows). They share the block-triangular core
`linearIndependent_sum_pinned_block` (RigidityMatrix.lean:1337) and the `q₀`-shear front matter, but
diverge irreducibly in conclusion.

**(c) Brick A — `le_finrank_span_rigidityRows_of_pinned_placement`** (RigidityMatrix.lean, beside the
splice brick; + an `_augment` variant routing through `linearIndependent_sum_pinned_block_augment`
:1481 for Case III's `+1`). Span-level, framework-agnostic; interface: a NEW block independent through
`single v`'s column (`hnewpin`) + an OLD block (a) vanishing on `v`'s column (`hold`), (b) independent
(`holdindep`), (c) in `span F.rigidityRows` (`hold_span`), with `hnew_span` for the NEW rows ⇒
`Nat.card ιn + Nat.card ιo ≤ finrank(span F.rigidityRows)`. Its proof IS L6b's `hrank_lb` skeleton
lifted out: `linearIndependent_sum_pinned_block` → `finrank_span_eq_card` → `Submodule.finrank_mono`
of the combined span. No new math; the genuinely-new content stays in the *callers'* discharge of
`hold_span` (see (d)). The arithmetic closes for both L6b (`hNpD`: `N + (D−1) = D(|V|−1) − k`, :4543)
and Case III (`(D−1)+1 + D(|V_Gv|−1) = D(|V|−1)`, the `_augment` `+1`).

**(d) Per-case transport-discharge map** (how each caller proves `hold_span`):
- **Lemma 6.8 / L6b** (`splitOff`): the `e₀ = e_a + e_b` row decomposition `he₀_rows_mem`
  (CaseI.lean:4380–4431) for the one fresh edge + the orientation-reconciling `hso_span` (:4443–4509)
  for non-`e₀` rows. **GENUINELY NEW** (the `e₀`-decomposition is the irreducible content; ≈130 lines).
- **Case III all-`k` / 22k** (`removeVertex`+relabel): the same content, **already isolated** as the
  `hρGv`/`hwmem` span-interface that W6b (`case_III_rank_certification`) consumes; at `k=0` from `h622`,
  at `k>0` from the deficient IH. Mechanical reuse — 22k's new content is the rank input (V8), not the
  placement.
- **Subgraph (`Gv ≤ G`, trivial):** `hold_span := Submodule.subset_span ∘ panelRow_mem_rigidityRows`,
  link via `IsSubgraph.isLink_iff hGv` — the rigid `case_II_placement_eq612`'s current membership step.
- **Case I (collapse): N/A — does not use Brick A** (see (e)).

**(e) Case I stays separate — verified, not a deficiency.** Case I's GP route uses the coupler
`hasGenericFullRankRealization_of_couple_blockTriangular_ofNormals_set`, whose surviving-block input is
**`(extProj sH).dualMap`-projected** rank (the contraction collapses a whole subgraph `H` to one body
`r` → projected-column geometry), not an unprojected `span F.rigidityRows` containment; its bare route
uses the splice brick (`hFc_surv_le`, the §1.66 dead-end for GP). Brick A's `single v` pin-a-body core
is the *splitting* tool; collapse needs the `extProj` tool. This is KT's own Lemma 6.2 vs 6.8
distinction, not a missing unification.

**(f) Retrofit & blueprint impact.** Brick A subsumes the *rank halves* of L6b (S4) and is what 22k's
Case III consumes. Brick B (`case_III_old_new_blocks`) is **kept** (different conclusion shape); its
deficiency-aware generalization (rank input + `hleG` transport) is **S3, deferred to 22k** (medium risk —
must not break `case_III_old_new_blocks_of_line`'s literal device-feed; speculative until 22k pins what
its rank path needs). **L6a (`case_II_placement_eq612_kdof`, CaseI.lean:3723–3910) retires** (dead — no
live Lean caller; its sole consumer `case_II_realization_all_k` inlines the steps, CaseI.lean:3921).
The rigid `case_II_placement_eq612` (CaseI.lean:3520) also has no live Lean caller but **must stay** —
it is the `\leanok` witness for `lem:case-II-realization-placement` (genericity-and-count.tex:248),
`\uses`'d across `case-iii.tex` (the 22k Case-III chain). **It is left untouched** — already green,
axiom-clean, and it is *not* re-routed through Brick A.

*Why no Brick-A re-route (the "option (i)" shape error, settled by recon 2026-06-14, verified against
the landed source).* Brick A's conclusion is **shape (A)** — a bare `N ≤ finrank(span F.rigidityRows)`
that *discards* the subfamily `finrank_span_eq_card` consumed internally. `case_II_placement_eq612`'s
conclusion is **shape (B)** — it *exposes* a literal independent `panelRow` subfamily `∃ s` of literal
`rigidityRows` (CaseI.lean:3546–3551), plus the companion `supportExtensor e_a ≠ 0` conjunct. Feeding
the rigid placement's blocks into Brick A yields only the finrank bound, **losing the `∃ s`** the
conclusion requires — Brick A's output is strictly weaker (and `card ≤ finrank` is the wrong direction
for the `Nat.card s ≥` lower bound). Recovering shape (B) needs the chain **Brick A →
`exists_independent_panelRow_subfamily_of_le_finrank`** (W6e, GenericityDevice.lean:718 — the
finrank→literal-subfamily extractor, which *does* exist and is exactly what the dead L6a used). But
that chain is **net worse**: a *double* extraction (Brick A throws away the family W6e re-extracts),
yielding a *less-structured* `s` (a fresh `Fin`-cut spanning family, not the current proof's structured
NEW(`e_b`-row)+OLD(IH-linking-rows) block decomposition), while still needing all the `q₀`-shear front
matter (`hane`/`hnewne`/`hgab`) for the `supportExtensor e_a ≠ 0` conjunct and for W6e's transversality
`hne` — so it adds work and removes structure, contradicting Brick A's "remove duplication" aim. The
§1.68(a) literal-brick anti-pattern (forcing a *caller* to re-derive) does not bite `case_II_placement_eq612`
either, since it has no caller. So the rigid decl stays on its current proof. One new blueprint node
`lem:rigidityRows-pinned-placement-rank-add` (rigidity-matrix.tex, beside the splice node
`lem:rigidityRows-splice-rank-add`).

**(g) Slice plan + open risks** (full layer plan + per-slice dispatch shape in `notes/Phase22j.md`):
S1 build Brick A (+`_augment`) → S2 blueprint node → S4 refactor L6b onto Brick A, extracting
`he₀_rows_mem` as the named `hold_span`-discharge helper (the one new-math slice) → S5 retire L6a
(delete the dead `case_II_placement_eq612_kdof`; the rigid `case_II_placement_eq612` is **left
untouched** — see (f): the "through Brick A" re-route was a shape error) → cleanup bundle (drop the L6b
`maxHeartbeats 3200000`/`longLine` suppressions; delete dead `hso_ne_sn` :4613 + stale comment block
:4628–4640 + stale TODO :4656; refresh the §C long-proof note). **Open risks** (need a build):
(i) Brick A's `Nat.card`/`Fintype` instance resolution across both call sites (L6b uses `Set`-subtype
indices, W6b uses `Fin`); (ii) S4 must preserve the `e₀`-decomposition's orientation case-split when
extracted. Both low-medium; S3's `_of_line`-preservation risk is 22k's, not 22j's.

### 1.69 The L7 signature pin — the Case-III rewire, `h622` *derived* from the all-`k` IH (`hsplitZero`): `case_III_realization` restates to carry the all-`k`-conditioned IH (mirroring 22i's reduction-case producers), the IH at the nested `k'`-dof `G_v` (`k' ≤ D−2`, `lem:case-III-gap3-minimalKDof` green) supplies the eq.-(6.22) lower bound `h622lb`; V8 RESOLVED — buildable, no motive change: UNLIKE L6 (whose IH seed coincides with the realization's, so it reads the bound off directly), L7's nested `G_v` realization is at its OWN seed while `h622lb` is wanted at the split realization's DIFFERENT seed, so the rank transfer IS the landed deficiency-aware rank-polynomial idiom (§1.62, `exists_rankPolynomial_of_le_finrank_linking` + footnote-6 non-root, NOT the `def=0`-only seed-rank bridge), with one genuinely-new sub-leaf (V8-a / L7a, P≈3): the non-relabel (`f=id`) rank-polynomial brick mirroring `exists_rankPolynomial_of_IH_relabel_linking`; no motive change beyond the §1.56 all-`k` IH restate (2026-06-15)

> **Docs-only design pass (the L7 pin), opus.** Every load-bearing decl below opened to its
> `def`/`theorem` body and verified against the cited claim (clause (i) of the dispatch). Landed
> source read this pass (post-22j-perf 5-file chain, current line numbers):
> CaseIII.lean — `case_III_realization` (:3831 — the **target**; its carried `h622` (:3835, the
> `∀ G v a b e₀ ends q, hrec → hgp → halg → finrank ≥ …` shape) and its **`k=0`-conditioned** IH
> `hIH` (:3847, `∀ G', G'.IsMinimalKDof n 0 → 2 ≤ ncard → smaller → Pc G'`); the body threads
> `h622` into `case_III_candidate_dispatch` (:3858) via `case_III_hsplit_producer`),
> `case_III_candidate_dispatch` (:3489 — its `h622lb` carry (:3504), instantiated at `(Q.ends, q)`
> with `q := fun p => Q.normal p.1 p.2` of the **split** realization `Q : Gab` (:3524, :3612), fed
> to W6b `exists_candidateRow_bottomRows_of_rigidOn`), the Claim-6.11 row helpers
> `exists_redundant_panelRow_ab_lam_of_rigidOn` (:304 — the **derivation engine**: it takes the
> *lower* bound `h622lb` (:315) and constructs the *equality* `h622` by setting
> `k' := D(m−1) − finrank(span R(G_v)-rows)` (:349) + the free upper bound via
> `span_rigidityRows_eq_sup_span_panelRow_edge` + `finrank_mono` (:347–352)) and
> `exists_candidateRow_bottomRows_of_rigidOn` (:385, the W6b consumer carrying `h622lb` :396);
> Theorem55.lean — `theorem_55_d3` (:483, the spine instance carrying `h622`/`h65`/`hsplit`/
> `hcontract` and threading `h622` into `case_III_realization` at :541; its `hsplitGP` slot of
> `theorem_55_generic`), `case_I_realization_all_k` (:1767 — the all-`k` GP producer TEMPLATE this
> mirrors: manufacture `ends = G.endsOf`, IH at the smaller graph at `k'`, read the deficient rank
> conjunct off the IH realization);
> CaseII.lean — `case_II_realization_all_k` (:297 — the **closest precedent**, L6: IH at the
> deficient `(k−1)`-dof split-off `Gab`, then it reads `N ≤ finrank(span R(Gab, q)-rows)` *directly*
> off the IH rank conjunct at `Q`'s own seed `q := Q.normal` (:440–495), realizing `G` at
> `q₀ = q[v ↦ shear]` — the SAME seed, NO polynomial transfer);
> CaseI.lean — the seed-rank bridge `isInfinitesimallyRigidOn_ofNormals_of_algebraicIndependent`
> (:2013, `lem:case-III-seed-rank-bridge`; transfers *full rigidity* `def=0`, eq. (6.18), between
> alg-indep seeds via the footnote-6 non-root device), `finrank_infinitesimalMotions_le_of_rankPolynomial_algebraicIndependent`
> (:2057, the `def>0` *upper*-bound counterpart), `exists_rankPolynomial_of_le_finrank_linking`
> (the L4b-1 rank-input rank-polynomial extractor; `GenericityDevice.lean:1488`, NO rigidity —
> `hN : N ≤ finrank(span …at q₀)` ⇒ a rational `Q` with `eval q₀ Q ≠ 0` and `∀ q, eval q Q ≠ 0 →
> N ≤ finrank(…at q)`), `exists_rankPolynomial_of_IH_relabel_linking` (:254 — the L5b-i
> *relabel* shared-core, `f`-mapped; takes `HasGenericFullRankRealization (Gc.map f)` and yields
> the rank polynomial for the `endsᵐ := f∘ends` selector via `finrank_span_rigidityRows_ofNormals_relabel_eq`
> :190 + `recordsLinks_agree_swap` :73 + `infinitesimalMotions_ofNormals_eq_of_ends_swap`),
> the selector-swap transport `recordsLinks_agree_swap` (:73);
> GenericityDevice.lean — `exists_independent_panelRow_subfamily_of_le_finrank` (:718, W6e, the
> finrank→literal-subfamily extractor `_of_le_finrank_linking` calls);
> ForestSurgery.lean — `splitOff_removeVertex_minimalKDof` (:3198, `lem:case-III-gap3-minimalKDof`:
> `G_v = G.removeVertex v` minimal `k'`-dof with `0 ≤ k' = def(G̃_v) ≤ D−2`, at `k=0`).
> PanelHinge.lean — `HasGenericFullRankRealization` (:1035 — `∃ Q, Q.graph = G ∧ GP ∧
> (finrank(span R) : ℤ) = screwDim k·(|V|−1) − G.deficiency ∧ link-recording ∧ AlgIndep ℚ q`).
> Blueprint read: `case-iii.tex` — `lem:case-III-nested-rank-lower` (:160, **red**, the L7 target;
> its proof prose already states the route: "Apply the all-`k` Theorem 5.5 to … `G_v` … then
> transfer the attained rank to the inductively-fixed seed"), `lem:case-III-gap3-minimalKDof`
> (:58, green), `lem:case-III-seed-rank-bridge` (:97, green), `lem:case-III` /
> `lem:case-II-realization` (:167). KT 2011 §6.4.1 read end-to-end against the PDF this pass
> (pp. 684–686): Claim 6.11, the nested IH (6.1) at `G_v`, eqs. (6.22)/(6.23); p. 680's `k=0`
> contrast confirming the redundant-`ab`-row machinery exists only because the `k=0` IH is rigid.
> No `.lean`/`.tex` edits this pass.

**The slot the L7 producer fills.** L7 is the `hsplitZero` arm of `theorem_55_generic` — the
landed 22h Case-III producer, restated. It is the `k=0` sibling of L6 (`case_II_realization_all_k`,
the `k>0` `hsplitPos` arm): both reduce by splitting off a degree-2 vertex, both reuse the
eq.-(6.12) placement; the difference is that the `k=0` IH at the split-off `Gab` is **rigid**
(`def=0`), giving only `(D−1) + D(|V∖v|−1) = D(|V|−1) − 1` — **one row short** (KT p. 680), so the
`k=0` Case III alone runs the whole Claim-6.11/6.12 redundant-`ab`-row machinery. That machinery is
already landed (22h, green-modulo `h622lb`); L7 does **not** rebuild it. L7's *only* job is to
**discharge the one carried inequality `h622lb`** by an all-`k` IH application at the nested `G_v`.

**(a) The corrected `case_III_realization` signature.** CaseIII.lean, restating the landed :3831.
The change is exactly two-fold: **drop the `h622` carry** and **promote the `k=0` IH to the all-`k`
IH** (the §1.56(c) motive shape, identical to `case_I_realization_all_k`'s/`case_II_realization_all_k`'s
`hIH`). Everything else (the `hD`/`hfresh` ambient data, the `hG`/`hV3`/`hnoRigid`/`hSimple`
hypotheses, the conclusion) is unchanged.

```lean
theorem PanelHingeFramework.case_III_realization [DecidableEq β] [Finite α] [Finite β]
    {n : ℕ} (hD : 6 ≤ Graph.bodyBarDim n)
    (hfresh : ∀ G' : Graph α β, ∃ e₀ : β, e₀ ∉ E(G'))
    (G : Graph α β) (hG : G.IsMinimalKDof n 0) (hV3 : 3 ≤ V(G).ncard)
    (hnoRigid : ∀ H : Graph α β, ¬ H.IsProperRigidSubgraph G n)
    (hSimple : G.Simple)
    -- the all-`k` IH (was: `∀ G', G'.IsMinimalKDof n 0 → …`); identical to L5/L6's `hIH`.
    (hIH : ∀ (k' : ℤ) (G' : Graph α β), G'.IsMinimalKDof n k' → V(G').Nonempty →
      V(G').ncard < V(G).ncard →
      (G'.Simple → PanelHingeFramework.HasGenericFullRankRealization 2 n G') ∧
        HasPanelRealization 2 n G') :
    PanelHingeFramework.HasGenericFullRankRealization 2 n G
```

Design notes: **(i)** `G` itself stays `IsMinimalKDof n 0` — L7 is the **`hsplitZero` slot**, the
`k=0` arm; the all-`k`-ness is needed only for the *nested* IH at `G_v` (which is `k'>0`-dof in
general), which the `k=0`-only IH cannot reach. **(ii)** the IH is the **conditioned pair** `Pc`
(GP-if-simple ∧ bare); L7 consumes its `.1` (GP) arm at `G_v` simple. **(iii)** consequential
**caller change at `theorem_55_d3` (:541) and `theorem_55_generic`'s `hsplitGP` slot**: the
`hsplitGP` slot of `theorem_55_generic` is currently `k=0`-IH-shaped — see (e)/§1.56(e); L7 either
(α) is invoked from a *new* all-`k` spine `theorem_55_all_k` (L9, where the `hsplitZero` slot's IH
IS the all-`k` `Pc`), or (β) `case_III_realization` is wrapped to down-cast the all-`k` IH it needs
from `theorem_55_d3`'s `k=0` IH — **impossible**, the `k=0` IH cannot supply `k'>0` instances. So
**L7 forces the spine to be all-`k`-conditioned at the `hsplitZero` slot**: this is the §1.56(e)
`theorem_55_all_k` spine, whose `hsplitZero` slot already hands the all-`k` `Pc` IH (L2's
`minimal_kdof_reduction_all_k` `hsplitZero` binder, §1.56(c)). **L7 lands the producer; L9 wires it
into `theorem_55_all_k`** (the spine restate is L9's job, §1.56(e)). At the L7 commit, the producer
stands alone with its all-`k` IH hypothesis; `theorem_55_d3` keeps carrying `h622` until L9 deletes
that carry by routing through `theorem_55_all_k`. *Flag F1 (not a blocker): if the L7 commit must
keep `theorem_55_d3` building, it threads `case_III_realization`'s old `h622`-carrying shape via a
thin `h622`-carrying wrapper until L9; the clean restate lands when L9 swaps the spine.* This is the
same staging L5/L6 used (the producer landed before its spine slot at L9).

**(b) The `h622lb` derivation (the heart of L7, KT eq. (6.22) at the nested IH).** Inside
`case_III_candidate_dispatch` (:3504), `h622lb` is the quantified obligation
```lean
∀ (ends : β → α × α) (q : α × Fin 4 → ℝ),
  (∀ e u w, (G.splitOff v a b e₀).IsLink e u w → ends e = (u, w) ∨ ends e = (w, u)) →
  (∀ x y : α, x ≠ y → LinearIndependent ℝ ![fun i => q (x, i), fun i => q (y, i)]) →
  AlgebraicIndependent ℚ q →
  screwDim 2 * (V(G.splitOff v a b e₀).ncard - 1) - (screwDim 2 - 2)
    ≤ Module.finrank ℝ (Submodule.span ℝ
        (PanelHingeFramework.ofNormals (G.removeVertex v) ends q).toBodyHinge.rigidityRows)
```
i.e. (writing `Gv := G − v`, `Gab := G.splitOff v a b e₀`, `m := |V(Gab)| = |V(Gv)|`, `D = screwDim 2 = 6`):
at any link-recording selector `ends` and any pairwise-LI, alg-indep seed `q`, the `Gv`-row span has
finrank `≥ D(m−1) − (D−2)`. Note the consumer instantiates this at `(Q.ends, q)` of the **split
realization** `Q : Gab` (:3612), where `q := fun p => Q.normal p.1 p.2` — so the `(ends, q)` is the
GP-Case-III producer's *own* construction, and `q` is alg-indep (`hQalg`) and pairwise-LI (`hQgp` GP).

The derivation, faithful to the green blueprint proof of `lem:case-III-nested-rank-lower` (:185):
1. **`Gv` is minimal `k'`-dof, `k' ≤ D−2`** — `splitOff_removeVertex_minimalKDof`
   (`lem:case-III-gap3-minimalKDof`, green) at `k=0`: `Gv.IsMinimalKDof n k'` with
   `k' := Gv.deficiency n`, `0 ≤ k' ≤ D−2`. (`Gv` nonempty: contains `a`; smaller: `|V(Gv)| = |V|−1`.)
2. **All-`k` IH at `Gv`.** `hIH k' Gv hk'min hGvne hGvlt` gives the conditioned pair; its `.1` at
   `Gv.Simple` (KT 6.7(ii) / `splitOff` simplicity from `hnoRigid`, residual leaf (b1)) gives
   `HasGenericFullRankRealization 2 n Gv` — a realization `Q_v : Gv` at rank
   `(finrank(span R(Gv, Q_v.normal)-rows) : ℤ) = D(m−1) − k'` (the rank conjunct), hence `≥ D(m−1) − (D−2)`.
3. **Transfer the attained rank to the given `(ends, q)`.** This is V8 — the rank `≥ D(m−1) − k'` at
   `Q_v`'s *own* seed must move to the *given* `(ends, q)` (the split realization's seed). The
   blueprint route (`lem:case-III-nested-rank-lower` proof) names "transfer by the footnote-6
   seed-transfer device" — but the seed-rank bridge `lem:case-III-seed-rank-bridge`
   (`isInfinitesimallyRigidOn_ofNormals_of_algebraicIndependent`) transfers **full rigidity**
   (`def=0`), which `Gv` at `k'>0` does **not** have. The honest rank-level transfer is the landed
   **deficiency-aware rank-polynomial** machinery (the §1.62 idiom, used by L4b/L5/L6):
   `exists_rankPolynomial_of_le_finrank_linking` (GenericityDevice:1488, NO rigidity) extracts from
   the `Q_v`-seed bound `N ≤ finrank(…at Q_v.normal)` (with `N := (D(m−1) − k').toNat`) a *rational*
   `Q_v`-rank-polynomial `P` with `∀ q', eval q' P ≠ 0 → N ≤ finrank(…at q')`; the given `q` is
   alg-indep, hence a non-root of the nonzero rational `P` (footnote 6,
   `MvPolynomial.eval_ne_zero_of_coeffs_subset_range_of_algebraicIndependent`); so `N ≤ finrank(…at q)`.

**(c) V8 — the one item with real proof-shape uncertainty, RESOLVED to a leaf, with a flagged
sub-leaf.** The verdict: V8 is **buildable from landed parts, no motive change** — but it carries
one genuinely-new wiring sub-leaf (P≈3), pinned below. The two halves:
* *The transfer mechanism is settled (the `exists_rankPolynomial_of_le_finrank_linking` chain of
  (b)3).* This is exactly the §1.62 deficiency-aware rank-polynomial idiom that L4b/L5/L6 already
  run; it is **rank-driven, not rigidity-driven**, so it tolerates the deficient `Gv`. The brick
  exists and is landed. (The seed-rank bridge `lem:case-III-seed-rank-bridge` is its `def=0`
  special case and is NOT the right tool here — flag this; the blueprint prose of
  `lem:case-III-nested-rank-lower` will need the citation corrected from "footnote-6 seed-transfer
  device" to the rank-polynomial extractor when the node flips green at L7, since the seed bridge
  only carries `def=0`.)
* *The selector mismatch is the genuinely-new sub-leaf (`V8-a`, P≈3).* `Q_v`'s rank conjunct is at
  `Q_v.ends` (records `Gv`'s links) and `Q_v.normal`; the obligation wants the bound at the *given*
  `ends` (records `Gab`'s links, hence `Gv`'s since `Gv ≤ Gab`) and `q`. Two adapters compose:
  (i) **selector swap** `Q_v.ends ↔ ends` — both record `Gv`'s links, so they agree up to swap;
  `recordsLinks_agree_swap` (CaseI:73) + `infinitesimalMotions_ofNormals_eq_of_ends_swap` (the
  motion-space-equality transport) carry the rank across, exactly the
  `finrank_span_rigidityRows_ofNormals_relabel_eq` (CaseI:190) shared-core pattern at `f = id`;
  (ii) **seed transfer** `Q_v.normal → q` — the (b)3 rank-polynomial non-root. The relabel core
  `finrank_span_rigidityRows_ofNormals_relabel_eq` does (i) and feeds (ii) for the *contraction*
  (`Gc.map f`, `f` the collapse); L7 needs the **`removeVertex`/plain-subgraph** analogue
  (`f = id`, `Gv ≤ Gab` a genuine subgraph). This is the V8-a leaf: a *non-relabel* rank-polynomial
  brick mirroring `exists_rankPolynomial_of_IH_relabel_linking` (CaseI:254) but at the identity map
  / plain selector. **Flag:** `Gv.map id = Gv` has no landed `map_id` reduction (grep found none),
  so the cleanest path is the dedicated non-relabel brick, not `f := id` into the relabel one.
  P≈3 — genuinely-new (the brick does not yet exist), but a near-mechanical mirror of the landed
  relabel one (route 2 of §1.62; the shared core + W6e + footnote-6 all landed). *Honest naming:
  this is the "real proof-shape uncertainty" the 22i hand-off flagged; the uncertainty is now
  localized to whether the non-relabel brick is a clean mirror (expected yes) vs needs a fresh
  selector-agreement argument (the residual risk).*

**(d) The L7 slice cut (build order).** Mirrors the L5b-ii / L6 cut: the new rank-transfer brick
first, then the producer restate.

* **L7a** — `PanelHingeFramework.exists_rankPolynomial_of_IH_linking` (CaseI.lean, beside the
  relabel sibling `exists_rankPolynomial_of_IH_relabel_linking` :254): the **non-relabel** (plain
  subgraph / `f = id`) deficiency-aware rank polynomial. **P≈3** (V8-a, genuinely-new but a
  near-mechanical mirror). Signature (the `f = id` specialization of :254 — drops the `Gc.map f`/
  `endsᵐ` machinery, keeps a parent link-recording `hends`):
  ```lean
  theorem PanelHingeFramework.exists_rankPolynomial_of_IH_linking
      [Finite α] [Finite β] (Gv : Graph α β) (ends : β → α × α)
      {n : ℕ} (hQvf : PanelHingeFramework.HasGenericFullRankRealization k n Gv)
      (hloop : Gv.Loopless)
      (hends : ∀ e u v, Gv.IsLink e u v → Gv.IsLink e (ends e).1 (ends e).2) :
      ∃ N : ℕ,
        (N : ℤ) = screwDim k * ((V(Gv).ncard : ℤ) - 1) - Gv.deficiency n ∧
        ∃ Q : MvPolynomial (α × Fin (k + 2)) ℝ,
          Q ≠ 0 ∧ (Q.coeffs : Set ℝ) ⊆ Set.range (algebraMap ℚ ℝ) ∧
          ∀ q : α × Fin (k + 2) → ℝ, MvPolynomial.eval q Q ≠ 0 →
            N ≤ Module.finrank ℝ (Submodule.span ℝ
              (PanelHingeFramework.ofNormals Gv ends q).toBodyHinge.rigidityRows)
  ```
  Body: the relabel core at `f = id` — a witness seed `nrm` (from `Q_v` via the selector-swap
  motion-space transport, the `_relabel_eq` :190 pattern specialized to `id`) where the finrank
  equals `N`, then `exists_rankPolynomial_of_le_finrank_linking` (GenericityDevice:1488) at
  `hN := le_refl N`. **No blueprint node** (churn-prone rank-polynomial infra, like the relabel
  sibling, which also has none). *Alternative if the witness-seed extraction is awkward at `id`:
  build `exists_rankPolynomial_of_IH_linking` directly from `Q_v`'s rank conjunct via the
  selector-swap span equality, skipping the `nrm`-witness detour — decide at the L7a build.*
* **L7b** — `PanelHingeFramework.case_III_realization` restated (the (a) signature), discharging
  `h622lb` by the (b) chain via L7a. **P≈2** (assembly: the `h622lb` lambda is L7a's `N`-bound →
  footnote-6 non-root → `≥ D(m−1) − (D−2)` via `k' ≤ D−2` arithmetic; everything else — the
  candidate dispatch, the Claim-6.11/6.12 machinery — is the **unchanged landed body**, since
  `case_III_candidate_dispatch` already consumes `h622lb` and L7 only changes how `h622lb` is
  *produced*). Restates `lem:case-III-nested-rank-lower` green (flip `\leanok`; correct the proof
  prose's seed-transfer citation per (c)) and drops the carried `h622` from `lem:case-III`'s pin.
  Statement-grep gate before commit (the `\lean{…case_III_realization}` survives the carry-drop;
  grep `blueprint/src` per `CLAUDE.md` *Structural-edit phases* — `lem:case-III` /
  `thm:theorem-55-d3-instance` state the `h622` carry, restate in the same commit).

**(e) What stays carried / what moves where.** L7 discharges `h622` (the `hsplitZero` carry,
`lem:case-III-nested-rank-lower`). It does **not** touch `h65` (L8, the Lemma-6.5 `hcontract` sub-arm)
or the spine wiring (L9 deletes the `h622`/`hsplit` carries from `theorem_55_d3` by routing through
`theorem_55_all_k`). The `b1` residual ("`Gv` simple from `hnoRigid`", KT 6.7(ii)) is a build-time
leaf, expected the same `splitOff`/`loopless` simplicity facts L6 uses (`case_II_realization_all_k`
:352–356 `splitOff_simple_of_noRigid` — but L7's `Gv = removeVertex`, so the simplicity is `G.Simple
→ (G − v).Simple`, immediate from `hSimple` via subgraph; *simpler than L6's*). At `k=0`, `Gv`'s
deficiency `k' = def(G̃_v)` can be `0` (then the IH leg is rigid and the transfer is the seed bridge's
`def=0` case) or `>0` — the rank-polynomial route (b)3 covers both uniformly, so no case split on `k'`.

**Estimate: ~2–3 commits.** L7a is the one genuinely-new brick (V8-a, the non-relabel rank
polynomial); L7b is the producer restate + the `h622lb` discharge assembly + the blueprint flip.
*Clause (ii) verdict: no motive/IH change beyond the §1.56 all-`k` IH restate (which L7 inherits
from the settled motive); no user adjudication needed.* The one honest flag is V8-a (P≈3, the
non-relabel rank-polynomial brick) — buildable from landed parts, not a research-shaped open
problem, but it is the leaf with the most build-time uncertainty (whether the relabel core
specializes cleanly to `f = id` vs needs a fresh selector-agreement argument).

**(f) Shape-match verification (clause (i)).** Confirmed against the landed source:
* The IH conclusion `HasGenericFullRankRealization` (:1035) carries the rank conjunct
  `(finrank(span R) : ℤ) = D(|V|−1) − deficiency` — a **`finrank` equality**, which yields the
  `finrank` *lower bound* `h622lb` requires (`≥ D(m−1) − (D−2)` via `k' ≤ D−2`). ✓ — the IH
  produces a `finrank` bound, `h622lb` consumes a `finrank` bound; no ∃-literal ⇄ `finrank`-bound
  mismatch. (The literal-`panelRow` ∃-subfamily that the *device* `hasFullRankRealization_of_independent_panelRow_index`
  needs is W6e's job *downstream* of `h622lb`, inside the unchanged `case_III_candidate_dispatch`
  body — L7 does not touch it.)
* `h622lb`'s RHS `finrank(span (ofNormals (G.removeVertex v) ends q).toBodyHinge.rigidityRows)` is
  exactly the span L7a's rank-polynomial brick bounds (same `ofNormals Gv ends q` shape). ✓
* The split realization's seed `q := fun p => Q.normal p.1 p.2` (:3524) is alg-indep (`hQalg`,
  `HasGenericFullRankRealization`'s :1042 conjunct) — the footnote-6 non-root input. ✓
* `splitOff_removeVertex_minimalKDof` (:3198) concludes `Gv.IsMinimalKDof n k' ∧ 0 ≤ k' ∧ k' ≤ D−2`
  at `k=0` — exactly the nested-IH input shape (the `k' ≤ D−2` is what makes `h622lb`'s
  `−(D−2)` lower bound the *weakest* of the family `−k'`). ✓

### 1.70 The L8 signature pin — the Lemma-6.5 arm, `h65` *discharged* via KT Claim 6.6 (graph side) + the Π°-placement producer (geometric side): the two-vertex-removal arm of the Case-I dispatch. KT Claim 6.6 FORCES `k = 0` (the hypotheses make `G` a 0-dof-graph), so the producer concludes inside the `k=0` stratum and discharges the `theorem_55_d3:516` 0-dof `h65` directly; the all-`k` `case_I_dispatch:1867` `h65` is discharged by the SAME producer after an internal `k = 0` derivation (its hypotheses force `def(G̃) = 0`). The geometric side IS the L6 Case-II template (Brick A `le_finrank_span_rigidityRows_of_pinned_placement` + the §1.62 deficiency-aware rank-polynomial transfer), with the NEW block being the TWO `v`-edges spanning the full `D` (KT Lemma 5.3, the one genuinely-new geometric sub-leaf) instead of L6's single split-off edge spanning `D−1`. V11 RESOLVED — buildable, NO motive/IH change: Claim 6.6 needs a NEW maximal-proper-rigid-subgraph existence lemma (genuinely-new combinatorics, bounded by `α` finite) and KT-Lemma-4.4 reused in the +`v` direction (the landed `removeVertex_deficiency_ge` is EXACTLY that direction). One privacy fix: de-privatize CaseIII's triple-LI bridge. **Loop-case refinement (c′), 2026-06-15:** the L8a-step-2 build surfaced that the maximal `G'` must be taken INDUCED (`G.induce V(G₀)`) to kill the contraction's loop mode — KT's silent edge-saturation; one more NEW brick `deficiency_le_deficiency_of_le_vertexSet_eq` (def antitone under edge addition at fixed vertex set). No definitional change. **Steps-3–5 pin (c″), 2026-06-15:** the `G''` carrier is `addEdge`-twice (`(G'.addEdge eₐ v a).addEdge e_b v b`, no bespoke def); step 4's minimality→graph-equality is ONE new brick `eq_of_isMinimalKDof_of_le_of_vertexSet_eq_of_isKDof` (a near-clone of the landed `edgeSet_ncard_le_two_of_isMinimalKDof_of_ncard_two` body), buildable, no motive/user decision (2026-06-15). **L8c geometric-core pin (i), 2026-06-15:** the Leaf-2 step-4 `hnewpin` (TWO `v`-edges spanning `D`) RE-RATED from (d)/(h)'s "build-time uncertainty leaf" to a pinned NEW `RigidityMatrix.lean` brick `exists_independent_pinned_two_edge_span_full` (P≈3.5, route via `finrank_sup_add_finrank_inf_eq` + `dualAnnihilator_sup_eq` + `exists_fun_fin_finrank_span_eq` — coordinator-verified consumer-fit against Brick A's verbatim `hnewpin`), and the `case_I_realization_h65` producer's exact Brick-A assembly pinned against Brick A's verbatim signature — template is `case_II_realization_all_k` (NOT `case_I_realization_all_k`, which uses the high-level coupler), OLD-block `hold_span` genuinely simpler (`G_v ≤ G` literal subgraph, one named seed-restriction `funext` flag), producer FORCES `ends eₐ=(v,a)`/`ends e_b=(v,b)` to avoid L6's swap branch. Buildable leaf sequence: L8c-1 `hnewpin` brick → L8c-2 producer + privacy + wiring. See §1.70(i)

> **Docs-only design pass (the L8 pin), opus.** Every load-bearing decl below opened to its
> `def`/`theorem` body and verified against the cited claim (clause (i)). Landed source read this
> pass (post-22j-perf chain, current line numbers):
> Theorem55.lean — `theorem_55_d3` (:483; its 0-dof `h65` carry at :516–:524, the **L8 discharge
> target**; the `hcontractGP` slot inlines the 6.3-vs-6.5 dispatch at :547–:556, the negative branch
> carrying `h65` at :555), `case_I_dispatch` (:1865; the **all-`k`** `h65` carry at :1867–:1875,
> consumed at :1893 in the simple branch's inner `by_cases hd` negative arm; this decl has NO live
> caller yet — it is the L9 spine's dispatch, the all-`k` sibling of `theorem_55_d3`'s inlined one),
> `case_I_realization_all_k` (:1769, the **template producer** the geometric side mirrors — IH at
> the smaller graph, Brick A for the rank, the §1.62 rank-polynomial transfer), `case_I_realization_nonsimple`
> (:1474, the L5a bare producer; the BodyHingeFramework-native assembly idiom), the `reaim`
> off-edge-selector micro-brick (:564);
> CaseII.lean — `case_II_realization_all_k` (:297, the **CLOSEST precedent**, L6: it consumes Brick A
> at :1063 with `Nat.card sn = D−1` NEW + `Nat.card so = N` OLD, then `exists_rankPolynomial_of_le_finrank_linking`
> for the seed transfer, then the `hne_G` extensor-nonzero discharge at :1088 — L8's geometric side
> is this template with the NEW block widened from `D−1` to `D`);
> RigidityMatrix.lean — `le_finrank_span_rigidityRows_of_pinned_placement` (:3344, **Brick A**, span-level
> `Nat.card ιn + Nat.card ιo ≤ finrank(span F.rigidityRows)`: NEW block `rn` independent through `v`'s
> column `hnewpin`, OLD block `ro` vanishing on `v`'s column `hold` + independent + in `span`; the L8
> geometric workhorse, KT eq. (6.10) shape), `finrank_hingeRowBlock` (:1129, each hinge block has
> finrank `D−1`), `eq_of_hingeConstraint_two_parallel` (:2672, takes `F : BodyHingeFramework k`, two
> edges `e₁ e₂` joining the SAME pair `u v` with LI extensors → `S u = S v`; Lemma 5.3 base, **but
> the SAME-pair shape — NOT directly the Π° distinct-endpoint shape**, see (d)), `span_inf_span_eq_bot_of_linearIndependent`
> (:2653, the `span C₁ ⊓ span C₂ = ⊥` core), `screwSpace_finrank` (:98, `finrank (ScrewSpace k) = screwDim k = D`),
> `exists_homogeneousIncidence_of_normals` (:456, the `d=3` homogeneous-incidence point builder
> consuming a `Fin 3 → Fin 4 → ℝ` triple-LI input);
> CaseIII.lean — `linearIndependent_normals_of_algebraicIndependent` (:3407, **`private`** — the
> triple-LI bridge `AlgebraicIndependent ℚ q → a,b,c distinct → LinearIndependent ℝ ![q(a,·),q(b,·),q(c,·)]`;
> consumed at :3658; the privacy is the one structural blocker, see (e)), `case_III_realization` (:3973,
> the L7-landed all-`k` Case-III producer — the parallel structural pattern: all-`k` IH + Brick-A-family
> rank + rank-polynomial transfer);
> SplitOffDeficiency.lean — `removeVertex_deficiency_ge` (:405, **KT Lemma 4.4**: degree-2 `v`,
> `D = bodyBarDim n ≥ 2` ⇒ `G.deficiency n ≤ (G.removeVertex v).deficiency n`; "vertex removal RAISES
> deficiency" — the exact direction Claim 6.6 needs, see (c) step 4);
> ForestSurgery.lean — `splitOff_removeVertex_minimalKDof` (:3198, `G−v` minimal `k'`-dof with `0 ≤ k' ≤ D−2`,
> at `k=0`; in Claim 6.6 `k' = 0` specifically since `G−v = G'` rigid);
> Deficiency.lean — `IsRigidSubgraph` (:417, `H ≤ G ∧ H.IsKDof n 0`), `IsProperRigidSubgraph` (:428,
> `IsRigidSubgraph ∧ 2 ≤ |V(H)| ∧ V(H) ⊂ V(G)`), `IsProperRigidSubgraph.vertexSet_nonempty` (:433);
> ReducibleVertex.lean — `simple_of_isMinimalKDof_of_noRigid` (:625, G0), `exists_adjacent_degree_two_pair`
> (:828, KT Lemma **4.6** — adjacent degree-2 *pair*; NOT Claim 6.6's single-vertex `v`, which comes
> from the maximal-subgraph construction, see (c) step 5);
> Operations.lean — `removeVertex` (:536), `removeVertex_le` (:553, `G−v ≤ G`), `vertexSet_removeVertex`,
> `removeVertex_isLink`;
> PanelHinge.lean — `HasGenericFullRankRealization` (:1035, the GP motive, conclusion of both `h65` shapes),
> `theorem_55_generic` (:1168, the 0-dof spine; its `hcontractGP` slot at :1190 is `k=0`-IH-shaped —
> the inlined dispatch lives here at the instance, NOT `case_I_dispatch`).
> Blueprint read: `case-i.tex` — `lem:case-I-dispatch` (:685, the **L8 target node, red**; its proof
> prose already names "Claim 6.6 + the Π°-placement … the obligation of sub-phase 22i" — the staleness
> the L8 commit reword fixes, `notes/Phase22k.md` *Blockers*), `lem:case-I-realization` (:589, green,
> the 6.3 arm), `lem:case-I-realization-nonsimple` (L5a, green). KT 2011 §6.2 read **against the PDF
> this pass** (pp. 676–677, pdf pages 30–31): **Lemma 6.5** statement (`k`-dof, `|V|≥3`, simple, has
> proper rigid subgraph, no proper rigid subgraph with simple contraction, (6.1) ⟹ a nonparallel
> realization at `rank = D(|V|−1) − k`); **Claim 6.6** (the maximal-subgraph argument forcing `G` 0-dof
> + the degree-2 `v` with `G−v` minimal 0-dof simple); the **Π°-placement** map `p` (= `q` off `{va,vb}`,
> `Π°∩Π(a)`/`Π°∩Π(b)` at the two `v`-edges where `Π°` is the non-parallel slack flat) and the **(6.10)
> block-triangular** rank chain (top `R(G,p;{va,vb},v)` rank `D` by Lemma 5.3, bottom `= R(G_v,q)` rank
> `D(|V∖v|−1)`, summing to `D(|V|−1)`). No `.lean`/`.tex` edits this pass.

**The slot the L8 producer fills.** L8 discharges `h65`, the negative arm of the Case-I dispatch's inner
`by_cases (G.rigidContract H r).Simple`: `G` is a *simple* minimal-dof-graph that *has* a proper rigid
subgraph but *no* proper rigid subgraph `H` (with rep `r`) whose contraction `G.rigidContract H r` is
simple. KT routes this (the Lemma-6.3 case-split failure) to **Lemma 6.5**, the vertex-removal argument.
L8 is the unchanged §1.54(a3) plan, re-validated against the landed all-`k` state below.

**(a) The two `h65` shapes RECONCILED — both target the SAME producer, the `k=0` derivation is internal.**
The coordinator flagged two distinct carried `h65` shapes. Read in full, they are:

* `theorem_55_d3:516` (**0-dof**): `∀ G, G.IsMinimalKDof n 0 → 3 ≤ |V| → (∃H, IsProperRigidSubgraph) →
  G.Simple → (∀H, IsProperRigidSubgraph → ∀r∈V(H), ¬(rigidContract H r).Simple) →
  (∀G', IsMinimalKDof n 0 → 2≤|V'| → smaller → Pc G') → HasGenericFullRankRealization 2 n G`.
  The conditioned IH is **`k=0`-only** (`G'.IsMinimalKDof n 0`).
* `case_I_dispatch:1867` (**all-`k`**): `∀ (k:ℤ) (G), G.IsMinimalKDof n k → 3 ≤ |V| → (∃H, …) → G.Simple →
  (∀H, … → ∀r∈V(H), ¬(rigidContract H r).Simple) → (∀ (k':ℤ) (G'), IsMinimalKDof n k' → Nonempty →
  smaller → Pc G') → HasGenericFullRankRealization 2 n G`. The IH is the **all-`k` `Pc`**, and the carried
  graph is `IsMinimalKDof n k` for an arbitrary `k`.

**The hand-off assertion "Claim 6.6 concludes inside the `k = 0` stratum, no all-`k` generality needed" is
CONFIRMED against KT.** Claim 6.6's *proof* (pdf p. 30): the maximal proper rigid subgraph `G'` is 0-dof
(Lemma 3.3); `G'' = G' + v + {e,f}` has `def(G̃'') ≤ def(G̃') = 0` by **Lemma 4.4**; maximality + minimality
force `V = V'∪{v}`, `G = G''`, so **`G` is a 0-dof-graph**. I.e. the `h65` hypothesis package (simple,
has-proper-rigid, all-contractions-non-simple) is *only satisfiable when `def(G̃) = 0`*. Consequence for
the all-`k` `case_I_dispatch:1867` `h65`: its carried `k` is forced `= G.deficiency n = 0` whenever the
hypotheses hold, so the producer's **first step derives `k = 0`** (from `hG : G.IsMinimalKDof n k` and the
Claim-6.6 graph conclusion `G.IsKDof n 0`, via the def-determines-`k` uniqueness of `IsMinimalKDof`) and
then runs the `k=0` argument. There is **no mismatch and no blocker**: one producer, `case_I_realization_h65`
(name indicative), discharges BOTH carries —
* `theorem_55_d3:516` calls it directly (the carry is already `k=0`-shaped; the IH it hands is `k=0`-only,
  which suffices because the *nested* IH application in L8 is at `G_v = G−v` which **is also 0-dof** here —
  unlike L7's Case III, where `G_v` is `k'`-dof and forced the all-`k` IH; see (d) step 3).
* `case_I_dispatch:1867` (when L9 wires it) calls the same producer after the internal `k = 0` derivation;
  the all-`k` IH it carries restricts to the `k'=0` instance the producer needs.

**This is the key structural finding distinguishing L8 from L7: L8 does NOT force the spine to be all-`k`.**
The `theorem_55_d3:516` `h65` is dischargeable *with only the `k=0` IH it already carries*, because both `G`
and `G_v` are 0-dof in Claim 6.6's stratum. So L8 lands a producer callable from BOTH the current
`theorem_55_d3` inlined dispatch (immediately, dropping that carry) and the future all-`k` `case_I_dispatch`
(at L9). *Decision for the coordinator/user: none forced* — the two shapes reconcile to one producer; L8
discharges `theorem_55_d3`'s `h65` now and leaves `case_I_dispatch`'s `h65` for L9's spine wiring (the same
staging L5/L6/L7 used: producer lands before its spine slot). **Flag (not a blocker):** if L8 wants to drop
`theorem_55_d3:516`'s `h65` carry in the same commit (cleaner), it rewrites the `:555` negative-branch lambda
to call `case_I_realization_h65` instead of the carried `h65` — a one-line wiring change. Recommended: do it,
since the producer concludes exactly the branch's `HasGenericFullRankRealization 2 n G`.

**(b) The L8 leaf decomposition (the §1.54(a3) steps 1–2, re-validated).** Two leaves + a wiring commit:
1. **Claim 6.6 graph side** (`exists_degree_two_removeVertex_of_no_simple_contraction`, name indicative)
   — NEW combinatorics, ~1–2 commits.
2. **The Π°-placement producer** (`case_I_realization_h65`) — geometric side, ~1–2 commits + a privacy fix.
3. **Wiring** — drop `theorem_55_d3:516`'s `h65` carry (rewrite the `:555` lambda); restate the
   `lem:case-I-dispatch` node green; reword the stale "obligation of sub-phase 22i" prose to 22k.

**(c) Leaf 1 — the Claim 6.6 graph-side lemma (NEW combinatorics).** This is the one genuinely-new
combinatorial content of L8. Pinned signature (lives in `ReducibleVertex.lean`, beside the other
degree-2/no-rigid existence lemmas, OR `Contraction.lean`; it is graph-only, no rigidity):

```lean
theorem Graph.exists_degree_two_removeVertex_of_no_simple_contraction
    [DecidableEq β] [Finite α] [Finite β] {G : Graph α β} {n : ℕ}
    (hD : 2 ≤ Graph.bodyBarDim n) (hV3 : 3 ≤ V(G).ncard)
    (hG : G.IsMinimalKDof n 0)                          -- NOTE: 0-dof; the all-`k` caller derives k=0 first
    (hSimple : G.Simple)
    (hrig : ∃ H : Graph α β, H.IsProperRigidSubgraph G n)
    (hnoSimpleContr : ∀ H : Graph α β, H.IsProperRigidSubgraph G n → ∀ r ∈ V(H),
      ¬ (G.rigidContract H r).Simple) :
    ∃ (v a b : α) (eₐ e_b : β),
      a ≠ v ∧ b ≠ v ∧ a ≠ b ∧ eₐ ≠ e_b ∧
      G.IsLink eₐ v a ∧ G.IsLink e_b v b ∧
      (∀ e x, G.IsLink e v x → e = eₐ ∨ e = e_b) ∧     -- `v` has degree exactly 2, with neighbours a,b
      (G.removeVertex v).IsMinimalKDof n 0 ∧            -- `G_v` minimal 0-dof (= the maximal subgraph G')
      (G.removeVertex v).Simple                          -- `G_v` simple (immediate from hSimple via removeVertex_le)
```

*The proof (KT Claim 6.6, pdf p. 30, faithful):*
1. **Take a vertex-inclusionwise maximal proper rigid subgraph `G'`.** *(LANDED + amended by (c′): the
   existence is `exists_maximal_isProperRigidSubgraph`, `Deficiency.lean:718`; (c′) replaces it by its
   INDUCED saturation `G' := G.induce V(G₀)` to kill the loop case — read (c′) for the live step 1.)*
   Since `α` is `Finite`, the proper rigid subgraphs are a finite nonempty (`hrig`) family; pick one of
   maximal `|V(H)|` (the landed `Nat.findGreatest`-bounded existence). `G'` is minimal 0-dof
   (`IsProperRigidSubgraph` ⟹ `IsKDof n 0`; minimality via `subgraph_minimality`/KT 3.3 since `G' ≤ G`).
2. **`G/E(G')` non-simple ⟹ a vertex `v ∈ V∖V'` with two edges into `V'`.** *(Bottom leaf LANDED
   (`rigidContract_not_simple`, `Contraction.lean:189`) + loop disjunct discharged by (c′)'s induced `G'`;
   read (c′) for the live step 2.)* From `hnoSimpleContr` at `(G', r)` for any `r ∈ V(G')`:
   `¬(G.rigidContract G' r).Simple`. `rigidContract_not_simple` unpacks this into a loop OR a parallel
   disjunct; on the INDUCED `G'` the loop disjunct is vacuous (`edgeSet_induce`, (c′)), so only the
   parallel disjunct — which (since `G` itself is simple, the multiplicity is created by the collapse)
   pulls back to a vertex `v ∉ V'` incident to two distinct edges `e, f` whose other endpoints lie in `V'`.
   *(The parallel-disjunct ⟹ shared-`v` extraction is the fiddliest sub-step, P≈3.)*
3. **`G'' = G' + v + {e,f}` is 0-dof (rigid) by KT Lemma 4.4.** `G''.removeVertex v = G'` (the two `v`-edges
   `e,f` and `v` are exactly what `G''` adds over `G'`). `removeVertex_deficiency_ge` (SplitOffDeficiency:405,
   the LANDED Lemma 4.4) at `G := G''`, `v := v` gives `G''.deficiency n ≤ (G''.removeVertex v).deficiency n
   = G'.deficiency n = 0`; with `deficiency_nonneg`, `def(G̃'') = 0`, so `G''.IsKDof n 0` — a rigid subgraph.
   **DIRECTION CONFIRMED:** Claim 6.6 wants `def(G̃'') ≤ def(G̃')` (adding `v`+2 edges does not raise
   deficiency); `removeVertex_deficiency_ge` states `def(G̃) ≤ def(G̃−v)`, i.e. with `G := G''` exactly
   `def(G̃'') ≤ def(G̃''−v) = def(G̃')`. The landed lemma is the right direction — NOT the converse.
   *(`removeVertex_deficiency_ge` needs `hdeg2`: `e,f` are the ONLY `v`-edges of `G''` — true by construction
   since `G''` adds only `e,f` at `v`.)*
4. **Maximality + minimality force `V = V'∪{v}` and `G = G''`.** `G''` is a rigid subgraph of `G` strictly
   larger than `G'` in vertices (`V'' = V'∪{v} ⊋ V'`); were `V'' ⊊ V`, `G''` would be a *proper* rigid
   subgraph larger than the maximal `G'` — contradiction. So `V'' = V`, i.e. `V = V'∪{v}`. Minimality of `G`
   (no edge removable) + `G'' ≤ G` + `def(G̃'') = 0 = def(G̃)` + same vertex set ⟹ `G = G''`. So `G` is 0-dof.
5. **`v` is degree-2, `G_v = G−v = G'` minimal 0-dof, simple.** `v`'s only `G''`-edges are `e,f` (degree 2);
   `G−v = G'' − v = G'`, the maximal subgraph, minimal 0-dof (step 1); simple by `hSimple.mono
   (G.removeVertex_le v)`. □
   *S/P/B note: Leaf 1 is **genuinely-new combinatorics** — the maximal-subgraph existence (step 1) and the
   non-simple-contraction ⟹ shared-`v` extraction (step 2) are the two real pieces; steps 3–5 are landed
   bricks (Lemma 4.4, `subgraph_minimality`, `Simple.mono`) + minimality bookkeeping. Bounded, research-free
   (no rigidity matrix, no genericity). The single P≈3 sub-step is step 2's contraction-non-simplicity
   unpacking; the rest is P≈2.*

**(c′) Loop-case resolution — take `G'` INDUCED (the L8a-build DESIGN-SETTLE, 2026-06-15, opus).**
The L8a-step-2-bottom-leaf build (commit 3693540, the landed `rigidContract_not_simple`,
`Contraction.lean:189`) surfaced that step 2 above is **incomplete as written**: it reads
"non-simplicity ⟹ a vertex `v ∈ V∖V'` with two edges into `V'`" (the *parallel* mode) and treats the
loop mode as not arising, but the landed brick exposes a genuine **second mode** that the
vertex-inclusionwise-maximal `G'` does NOT exclude. This subsection settles the route; it amends
step 2 — it does **not** open a new leaf inventory (the (f) slice cut stands).

*The gap, re-verified against landed source (clause (i)).* `rigidContract_not_simple` (the
contrapositive of `rigidContract_simple`, via the abstract `map_not_simple`, all in `Contraction.lean`)
unpacks `¬(G.rigidContract H r).Simple` into **two** disjuncts on the surviving graph
`G.deleteEdges E(H)` (whose links are `G`-links off `E(H)`, `deleteEdges_isLink`):
* **loop**: `∃ e x y, (G ＼ E(H)).IsLink e x y ∧ collapseTo r V(H) x = collapseTo r V(H) y`;
* **parallel**: two *distinct* surviving edges with collapsed-equal end-pairs.

`collapseTo r V(H) = fun x => if x ∈ V(H) then r else x` (`ReducibleVertex.lean:1042`, verified). So
for a surviving-edge link with `x ≠ y` (a *simple* `G` supplies `x ≠ y` from `IsLink.ne`),
`collapseTo x = collapseTo y` ⟺ **both `x, y ∈ V(H)`** (the only fiber `collapseTo` merges two distinct
points into is `r`, reached exactly from inside `V(H)`; the mixed and both-outside cases are
contradictory). The loop case is therefore *precisely* a `G`-edge with both endpoints in `V(G')` that is
**not** in `E(G')` — and it IS reachable, because `IsRigidSubgraph`/`IsProperRigidSubgraph`
(`Deficiency.lean:417/428`, `H ≤ G ∧ H.IsKDof n 0` — re-read this pass) are **plain subgraphs, NOT
induced**: an edge of `G` inside `V(G')` need not lie in `E(G')`. KT's own proof (pdf p. 30, re-read this
pass — offset `paper p.N = pdf page N−646`) takes `G'` *vertex-inclusionwise maximal* and asserts the
parallel conclusion ("a vertex `v ∈ V∖V'` and two edges `e, f` incident to `v` and some other vertices of
`V'`") **directly** — silently assuming the loop mode away. The hole in KT-as-literally-written: if a
`G`-edge `g` lies inside `V(G')` off `E(G')`, then `G' + g` (edge-augment, *same vertex set*) is also a
rigid (def antitone under edge addition, below) proper subgraph, so KT's `G'' = G' + v + {e,f}` is not the
only larger rigid subgraph — `G' + g` is one too, at the *same* vertex cardinality, which neither
vertex-inclusionwise nor vertex-cardinality maximality forbids. So **the parallel-only reading needs the
maximal `G'` to be edge-saturated within its vertex set, i.e. INDUCED.** This is also why
`exists_maximal_isProperRigidSubgraph` (`Deficiency.lean:718`, the landed step 1) does not by itself close
the gap: it returns a vertex-cardinality-maximal proper rigid *subgraph*, and `G'+g` is rigid, proper, and
of the same vertex cardinality, so maximality is silent on it.

*The resolution: route through the INDUCED saturation `G' := G.induce V(G₀)`.* `G.induce X` carries
**exactly** the `G`-edges with both ends in `X` (`Delete.lean:151`, `IsLink e x y := G.IsLink e x y ∧ x ∈
X ∧ y ∈ X`, verified) — so for an induced `G'` there is **no** surviving edge `∈ E(G) ∖ E(G')` with both
ends in `V(G')`, and the loop disjunct of `rigidContract_not_simple` becomes vacuous. Concretely Leaf 1's
step 1 is amended to a **two-move** opener:
1a. `exists_maximal_isProperRigidSubgraph hrig` (landed, **reused as-is, no restrengthening**) gives a
   vertex-cardinality-maximal proper rigid subgraph `G₀`.
1b. Replace `G₀` by its **induced saturation** `G' := G.induce V(G₀)`. Then (i) `V(G') = V(G₀)`
   (`induce_vertexSet`/`vertexSet_induce`), so `G'` keeps `G₀`'s cardinality-maximality and properness
   (`2 ≤ |V| `, `V(G') ⊊ V(G)`); (ii) `G₀ ≤ G'` (same vertex set, every `G₀`-edge lies inside `V(G₀)`,
   hence in `E(G')`); (iii) `G'` is rigid via the **NEW brick** (def antitone under edge addition at a
   fixed vertex set): `def(G'̃) ≤ def(G₀̃) = 0`, and `≥ 0` (`deficiency_nonneg`), so `= 0`.
With `G'` induced, step 2 takes ONLY the parallel disjunct — the loop disjunct is discharged by
"`G.IsLink g x y ∧ g ∉ E(G') ∧ x,y ∈ V(G')`" contradicting `edgeSet_induce` (every such `g ∈ E(G')`).
The parallel disjunct then yields a vertex `v ∉ V(G')` with two distinct edges into `V(G')` *exactly as
step 2 originally claimed*. Steps 3–5 are UNCHANGED (they consume `G'` only through its vertex set + the
two `v`-edges; the maximal-subgraph maximality used in step 4 is `G'`'s, inherited from `G₀`'s in 1a).

*The NEW brick (pin its exact signature — it is genuinely new, grep clean: no `deficiency`-antitone-
under-edge-addition / `induce`-`IsKDof` lemma in tree).* Lives in `Deficiency.lean` (it is about
`deficiency`, beside `subgraph_minimality`):
```lean
-- LANDED (04a5330): the pin below omitted `[Finite β]` + `hD : 1 ≤ bodyBarDim n`; both added at
-- the build (the L8a-0 boundary pair, sonnet+opus, independently corrected to this — `[Finite β]`
-- for the larger crossing-set `ncard`, `hD` for `D−1 ≥ 0`, the conclusion being false at `n=0`).
-- Both already present on every caller (Leaf-1 has `[Finite β]` + `hD : 2 ≤ …`).
theorem Graph.deficiency_le_deficiency_of_le_vertexSet_eq [Finite α] [Finite β]
    {H H' : Graph α β} {n : ℕ} (hD : 1 ≤ bodyBarDim n)
    (hle : H ≤ H') (hV : V(H) = V(H')) :
    H'.deficiency n ≤ H.deficiency n
```
*Proof (small, ~P≈2):* for every labeling `f`, `numParts H' f = numParts H f` (equal vertex sets, the
`f '' V(·)` images agree), while `crossingEdges H f ⊆ crossingEdges H' f` (an `H`-edge crossing `f` is an
`H'`-edge crossing `f`, since `H ≤ H'`; `H'` may have *more* crossing edges) ⟹ since `partitionDef G n f =
D(numParts−1) − (D−1)·|crossingEdges|` is **decreasing in the crossing count**, `partitionDef H' n f ≤
partitionDef H n f`; take `ciSup` (`bddAbove_range_partitionDef` + `partitionDef_le_deficiency`) to get
`def(H') ≤ def(H)`. (`D = bodyBarDim n ≥ 1` keeps the `(D−1)` coefficient `≥ 0`; the molecular regime
`D ≥ 3` is available but only `D ≥ 1` is needed.) The induced wrapper feeds it `H := G₀`, `H' := G' =
G.induce V(G₀)`, `hle := G₀ ≤ G.induce V(G₀)` (the same-vertex-set edge containment), `hV` from
`vertexSet_induce`.

*Leaf-1 signature delta.* The pinned signature in (c) is **unchanged** — the conclusion's
`(G.removeVertex v).IsMinimalKDof n 0` etc. still hold (with `G−v = G'` the *induced* maximal subgraph). The
only change is internal: step 1 becomes 1a+1b, and step 2 discharges the loop disjunct via
`edgeSet_induce`. No new hypothesis on the lemma; `exists_maximal_isProperRigidSubgraph` is reused as-is.

*LANDED (2026-06-15): steps 1a+1b packaged as `exists_maximal_induced_isProperRigidSubgraph`
(`Deficiency.lean:798`, axiom+warning+lint clean) — returns a vertex-maximal AND induced-saturated
proper rigid `G'` (saturation = step 2's `hHsat`), so the Leaf-1 thread takes the opener as a single
call. The remaining steps 3–5 surfaced a NOT-yet-landed brick the (c) prose glossed: step 4's
"minimality of `G` ⟹ `G = G''`" needs an `IsMinimalKDof` → graph-equality bridge (minimality is
matroid-base-meets-fiber, not "no edge removable") — a removable `G`-edge off `E(G'')` would give an
`M(G̃)`-base avoiding its fiber, contradicting minimality. P≈3 matroid-counting, design before the
steps-3–5 build (`Deficiency.lean`, beside `subgraph_minimality`).*

*Clause (ii) — what is NOT triggered.* This is **not** a definitional change to `IsRigidSubgraph` (the
fix takes a *particular* induced rigid subgraph; the predicate stays the plain-subgraph one, so no existing
consumer of `IsRigidSubgraph`/`IsProperRigidSubgraph` is touched). The NEW brick is bounded project-side
linear-counting, not research-shaped. KT's argument is matched (induced = KT's silent edge-saturation of
the maximal `G'`); no open decision for the coordinator/user. **One ordering consequence:** the NEW brick
`deficiency_le_deficiency_of_le_vertexSet_eq` is a `Deficiency.lean` leaf with no `rigidContract`/rigidity
dependency, so — like step 1's `exists_maximal_isProperRigidSubgraph` — it can land FIRST as its own
commit (the next concrete commit; see *Hand-off*), before the full Leaf-1 assembly that consumes it.

**(c″) Leaf-1 steps 3–5 pin — the carrier `G''` + the minimality→equality brick + the assembly
(DESIGN-SETTLE, 2026-06-15, opus, docs-only).** The opener (1a+1b, `exists_maximal_induced_isProperRigidSubgraph`)
and the extraction (step 2, `exists_isLink_pair_of_rigidContract_not_simple`) are landed, so steps 3–5 are
the remaining build. The (c) prose glossed two things — the `G''` *carrier* (`G' + v + {eₐ, e_b}` has no
add-vertex-and-edges in the Graph API) and step 4's *minimality→graph-equality* bridge. Both are settled
below, every load-bearing decl opened to its body this pass (clause (i)).

*The carrier — `addEdge`-twice, no bespoke def needed.* The package has `Graph.addEdge (G : Graph α β)
(e : β) (a b : α) := singleEdge a b e ∪ G` (`.lake/packages/Matroid/…/Subgraph/Defs.lean:551`,
`@[simps! edgeSet vertexSet]`). Pin
```lean
G'' := (G'.addEdge eₐ v a).addEdge e_b v b
```
where `G'` is the opener's induced-saturated maximal proper rigid subgraph and `v, a, b, eₐ, e_b` come from
the extraction. Verified semantics (the four (c) facts):
- **(i) `V(G'') = V(G') ∪ {v}`.** `addEdge` is `singleEdge a b e ∪ G`, and `vertexSet_union` (Defs.lean:461,
  `rfl`) + `singleEdge`'s `vertexSet = {a,b}` (Constructions/Basic.lean:48–49) give
  `V(G'') = {v,b} ∪ ({v,a} ∪ V(G'))`. With `a, b ∈ V(G')` (extraction) this is `V(G') ∪ {v}`. The `simps!`-generated
  `addEdge_vertexSet` automates it.
- **(ii) `v` has degree EXACTLY 2 in `G''` (only `eₐ, e_b`).** `eₐ ∉ E(G')` and `e_b ∉ E(G')` because each is a
  `v`-edge and `v ∉ V(G')` (extraction) — so an `E(G')`-edge can't be incident to `v`, and `eₐ ≠ e_b` (extraction)
  means the second `addEdge`'s base `(G'.addEdge eₐ v a)` carries `eₐ ∉` its-edge-set-minus-`{e_b}` cleanly. A
  `G''`-link `f v x` is, by `addEdge_isLink_iff_of_notMem` (Defs.lean:566, **no `DecidableEq` needed**) applied
  twice, either `f = e_b ∧ {v,b}=…`, or `f = eₐ ∧ {v,a}=…`, or a `G'`-link at `v` (impossible, `v ∉ V(G')`). So
  `∀ f x, G''.IsLink f v x → f = eₐ ∨ f = e_b` — exactly `removeVertex_deficiency_ge`'s `hdeg2` at `G := G''`.
- **(iii) `G''.removeVertex v = G'`.** `removeVertex v = G'' - {v} = G''[V(G'')∖{v}]` (`deleteVerts_def`); since
  `v ∉ V(G')`, `V(G'')∖{v} = V(G')`. Prove by `ext_of_le_le` (Subgraph/Basic.lean:65, `≤`+`V`-eq+`E`-eq ⟹ eq)
  OR directly `Graph.ext`: vertex sets agree (`deleteVerts_vertexSet`); a `(G''-{v})`-link `f x y` is a `G''`-link
  with `x,y ≠ v` (`deleteVerts_isLink_iff`, Defs.lean:86) — the two added edges are `v`-incident so are dropped,
  leaving exactly the `G'`-links, and conversely every `G'`-link survives (its ends ≠ `v`). **This direction is
  the one place saturation is load-bearing:** `G''[V(G')]` keeps every `G''`-edge inside `V(G')`, which are the
  `G'`-edges *only because `G'` is induced* (`G' = G[V(G₀)]`, so `G'[V(G')] = G'` by
  `IsInducedSubgraph.vertexSet_induce_eq`, Delete.lean:399) — a non-saturated maximal `G₀` would let a `G`-edge
  inside `V(G₀)` off `E(G₀)` leak in. The opener's saturation conjunct is consumed here, not only at step 2.
- **(iv) `G'' ≤ G`.** `addEdge_le (hle : H ≤ G) (he : G.IsLink e x y) : H.addEdge e x y ≤ G` (Defs.lean:581),
  twice: `eₐ, e_b` are real `G`-edges (`G.IsLink eₐ v a`, `G.IsLink e_b v b` from the extraction), and `G' ≤ G`
  (opener). No label collision (`eₐ, e_b ∉ E(G')`, and `eₐ ≠ e_b`).

*The minimality→graph-equality brick (genuinely new, but a near-CLONE of a landed lemma — buildable, NOT
research-shaped).* Step 4 needs `E(G) = E(G'')` (then `G = G''` by `ext_of_le_le` from `G'' ≤ G` + `V(G) =
V(G'')`). `IsMinimalKDof`'s minimality is matroid-base-meets-every-edge-fiber (`Deficiency.lean:359`,
re-read), not "no edge removable". **Decisive finding:** the EXACT argument is already in tree as
`edgeSet_ncard_le_two_of_isMinimalKDof_of_ncard_two` (`Deficiency.lean:2253`) — the new brick is its body with
the avoided edge generalized from "the 3rd of three parallel edges" to "any `g ∈ E(G) ∖ E(G'')`". Pin (lives in
`Deficiency.lean`, beside `subgraph_minimality`; conclude `G = G''` directly so the caller gets the assembly's
hinge fact in one step):
```lean
theorem Graph.eq_of_isMinimalKDof_of_le_of_vertexSet_eq_of_isKDof
    [DecidableEq β] [Finite α] [Finite β] {G G'' : Graph α β} {n : ℕ}
    (hD : 1 ≤ bodyBarDim n) (hG : G.IsMinimalKDof n 0) (hle : G'' ≤ G)
    (hV : V(G'') = V(G)) (h0 : G''.IsKDof n 0) : G = G''
```
*Proof route (verified, every step has its lemma):* `V(G).Nonempty` from `hV3`/`hG`. Suppose `g ∈ E(G)`,
`g ∉ E(G'')`. Get a base `B'' of M(G̃'')` (`exists_isBase`); `|B''| = D(|V''|−1)` via
`isBase_ncard_add_deficiency_eq` at `def(G̃'')=0` (`h0`). `B''` is `M(G̃)`-independent via
`matroidMG_restrict_mulTilde hle` + `restrict_indep_iff` (the precedent's `hBindep` step). rank `M(G̃)` =
`D(|V|−1)` via `rank_add_deficiency_eq` at `def(G̃)=0` (`hG.1`); with `V'' = V` (`hV`), `|B''| = rank M(G̃)`, so
`B''` is an `M(G̃)`-base (`Indep.isBase_of_ncard`, using `Indep.ncard_le_rank` + the size equality, exactly the
precedent's `hBbase`). `hG.2 B'' hBbase g (hg_mem)` forces `B'' ∩ edgeFiber g ≠ ∅`; but `B'' ⊆ E(G̃'')`
(`IsBase.subset_ground`) and `edgeFiber g` is disjoint from `E(G̃'')` (a copy `p` with `p.1 = g ∉ E(G'')` is not
in `E(G̃'') = mem_edgeSet_mulTilde`), contradiction (the precedent's final `simp_all`). So `E(G) ⊆ E(G'')`;
with `hle.edgeSet_mono` (`E(G'') ⊆ E(G)`) get `E(G) = E(G'')`, then `ext_of_le_le hle le_rfl hV.symm hEeq.symm`.
**No fact absent from tree** — `isBase_ncard_add_deficiency_eq`, `matroidMG_restrict_mulTilde`,
`rank_add_deficiency_eq`, `Indep.isBase_of_ncard`, `Indep.ncard_le_rank`, `mem_edgeSet_mulTilde`, `edgeFiber`,
`ext_of_le_le` all confirmed present this pass. (`[Finite α] [Finite β] [DecidableEq β]` + `hD` all on every
caller; the precedent carries the same.)

*The steps-3–5 assembly (how it composes to the Leaf-1 conclusion).* Inside
`exists_degree_two_removeVertex_of_no_simple_contraction`:
1. **Opener (step 1):** `exists_maximal_induced_isProperRigidSubgraph hD'.le hrig` (`hD' : 1 ≤ bodyBarDim n` by
   `omega` from `hD : 2 ≤`) → `G'` proper rigid, vertex-cardinality-maximal, induced-saturated.
2. **Extraction (step 2):** `V(G').Nonempty` (from `2 ≤ |V(G')|`) gives an `r ∈ V(G')`;
   `exists_isLink_pair_of_rigidContract_not_simple hr hHsat (hnoSimpleContr G' hG'prop r hr)` (its `hHsat` = the
   opener's saturation conjunct; `[G.Simple]` from `hSimple`) → `v ∉ V(G')`, distinct `eₐ:v–a`, `e_b:v–b`,
   `a, b ∈ V(G')`, `a ≠ b`, `a ≠ v`, `b ≠ v`, `eₐ ≠ e_b`.
3. **Carrier (step 3):** set `G''` (above). `def(G̃'') = 0`: `removeVertex_deficiency_ge hD … hdeg2` (carrier
   (ii)) at `G := G''` gives `def(G̃'') ≤ def(G̃''−v) = def(G̃') = 0` (carrier (iii) + `G'` rigid), and
   `deficiency_nonneg` pins `= 0`. So `G''.IsKDof n 0`.
4. **Maximality forces `V(G'') = V(G)` (step 4a).** `G''` is rigid (step 3), `V(G'') = V(G')∪{v} ⊋ V(G')`
   (carrier (i)). If `V(G'') ⊊ V(G)` then `G''.IsProperRigidSubgraph G n` with `|V(G'')| = |V(G')|+1 >
   |V(G')|` — contradicting the opener's cardinality-maximality. So `V(G'') = V(G)` (`Set.eq_of_subset_of_ncard_le`
   / the `⊂`-vs-`=` dichotomy on `V(G'') ⊆ V(G)`). **Then the new brick (step 4b):**
   `eq_of_isMinimalKDof_of_le_of_vertexSet_eq_of_isKDof hD'.le hG (addEdge_le-twice) hVeq h0` → `G = G''`.
5. **Conclusion (step 5).** With `G = G''`: `v` degree-exactly-2 (carrier (ii), transported `G''→G`);
   `G.removeVertex v = G''.removeVertex v = G'` (carrier (iii)), which is minimal 0-dof
   (`subgraph_minimality (removeVertex_le ..) hG (G'.IsKDof n 0)`) and simple (`hSimple.mono (removeVertex_le ..)`).
   Pack `v, a, b, eₐ, e_b` + the conjuncts.

*S/P/B note.* Steps 3–5 are now ALL landed-brick + bookkeeping: the carrier is `addEdge`+package lemmas, the
new brick is a near-clone of `edgeSet_ncard_le_two_of_isMinimalKDof_of_ncard_two` (P≈3 but copy-shaped, not
research), and the assembly is composition. **Nothing forces a motive/definitional change or a user decision**
(clause (ii) not triggered). The one ordering call: land the new brick
`eq_of_isMinimalKDof_of_le_of_vertexSet_eq_of_isKDof` FIRST as its own `Deficiency.lean` commit (self-contained
matroid-counting, no `rigidContract`/carrier dependency), then the full Leaf-1 assembly.

**(d) Leaf 2 — the Π°-placement producer (geometric side, the L6 template widened).** Pinned signature
(lives in `Theorem55.lean`, beside `case_I_realization_all_k`/`case_I_dispatch`, so it threads into the
dispatch's negative branch; needs the (e) privacy fix to call the triple-LI bridge):

```lean
theorem PanelHingeFramework.case_I_realization_h65
    [DecidableEq β] [Finite α] [Finite β] {n : ℕ}
    (hD : 6 ≤ Graph.bodyBarDim n) (hn : Graph.bodyBarDim n = screwDim 2)
    (hfresh : ∀ G' : Graph α β, ∃ e₀ : β, e₀ ∉ E(G'))
    (G : Graph α β) (hG : G.IsMinimalKDof n 0) (hV3 : 3 ≤ V(G).ncard)
    (hrig : ∃ H : Graph α β, H.IsProperRigidSubgraph G n) (hSimple : G.Simple)
    (hnoSimpleContr : ∀ H : Graph α β, H.IsProperRigidSubgraph G n → ∀ r ∈ V(H),
      ¬ (G.rigidContract H r).Simple)
    (hIH : ∀ G' : Graph α β, G'.IsMinimalKDof n 0 → 2 ≤ V(G').ncard →
      V(G').ncard < V(G).ncard →
      (G'.Simple → PanelHingeFramework.HasGenericFullRankRealization 2 n G') ∧
        HasPanelRealization 2 n G') :
    PanelHingeFramework.HasGenericFullRankRealization 2 n G
```

This matches `theorem_55_d3:516`'s `h65` carry *exactly* (same hypotheses, same conclusion) — so the L8
wiring is `theorem_55_d3`'s `:555` lambda calling `case_I_realization_h65 hD hn hfresh G hG hV3 hrig hSimple
(fun H hH r hr hcs => …) hIH` (the `hnoSimpleContr` repackaged from the dispatch's `(fun H hH r hr hcs =>
hd ⟨…⟩)`). The IH is the **`k=0`-only** form (matching `theorem_55_d3`'s carry); for the all-`k`
`case_I_dispatch:1867` caller, a thin wrapper restricts the all-`k` `Pc` IH to its `k'=0` instances and
derives `k = 0` first.

*The body (KT Lemma 6.5 + (6.10), faithful — the L6 `case_II_realization_all_k` template widened):*
1. **Claim 6.6 graph side (Leaf 1).** `exists_degree_two_removeVertex_of_no_simple_contraction hD'.le hV3 hG
   hSimple hrig hnoSimpleContr` gives `v, a, b, eₐ, e_b` with `v` degree-2, `G_v := G−v` minimal 0-dof,
   simple. (`hD' : 2 ≤ bodyBarDim n` by `omega` from `hD : 6 ≤`.)
2. **IH at `G_v` (the `k=0` arm).** `G_v` is minimal 0-dof, smaller (`|V(G_v)| = |V|−1 < |V|`, via
   `vertexSet_removeVertex` + `Set.ncard_diff_singleton`), `2 ≤ |V(G_v)|` (`= |V|−1 ≥ 2` from `hV3`), and
   simple (Leaf 1). So `(hIH G_v hG_v hV_v hlt).1 hG_v.Simple` gives `HasGenericFullRankRealization 2 n G_v`
   — a realization `Q_v : G_v` at rank `D(|V_v|−1) − G_v.deficiency = D(|V_v|−1)` (since `G_v` 0-dof), with
   GP (pairwise-LI normals) + alg-indep seed `q_v := fun p => Q_v.normal p.1 p.2`.
   *Note: UNLIKE L7's Case III — where the nested `G_v` is `k'`-dof and forced the all-`k` IH — here `G_v`
   is **0-dof** (it equals the maximal rigid subgraph `G'`), so the `k=0`-only IH suffices. This is why L8
   does not force the all-`k` spine.*
3. **Build `Q : G` at the SAME seed, with `v`'s two normals via the Π° slack flat.** Realize `G` on
   `q := q_v` extended at `v`: set `Q.normal v := <the Π° normal>`, a fresh normal making the triple
   `![q(v,·), q(a,·), q(b,·)]` LI (KT's `Π°`: a `(d−1)`-flat not parallel to any `Π_{G_v,q}(u)` and not
   containing `Π(a)∩Π(b)`). The seed `q` extended at `v` stays alg-indep / pairwise-LI; the triple-LI is
   the §1.53 bridge `linearIndependent_normals_of_algebraicIndependent` at `(a,b,c) := (v,a,b)` (this is
   why the privacy fix (e) is needed). Selector `Q.ends` overridden at `eₐ, e_b` (the `reaim`/`Function.update`
   pattern at :564) to record `(v,a)`, `(v,b)`; off the two `v`-edges, `Q.ends = Q_v.ends` (records `G_v`'s
   links, hence `G`'s away from `v`).
4. **Rank `≥ D(|V|−1)` via Brick A** (KT (6.10) block-triangular). The NEW block `rn` = the two `v`-edge
   hinge rows (`va`, `vb`), an independent subfamily of size `D` through `v`'s screw column (`hnewpin`,
   `Nat.card ιn = D`); the OLD block `ro` = `Q_v`'s `D(|V_v|−1)` rows, vanishing on `v`'s column (`hold`:
   `G_v`-rows don't touch `v`) + independent + in `span Q.toBodyHinge.rigidityRows` (`hold_span`: the
   `removeVertex_le` subgraph membership, `Submodule.subset_span ∘ panelRow_mem_rigidityRows`, the TRIVIAL
   `Gv ≤ G` discharge of §1.68(d) — `G_v ≤ G` is a genuine subgraph, NOT a collapse/splitOff, so the OLD-row
   transport is the *easy* case). `le_finrank_span_rigidityRows_of_pinned_placement Q.toBodyHinge (v := v)
   hold hnewpin holdindep hnew_span hold_span` gives `D + D(|V_v|−1) ≤ finrank`, i.e. `D(|V|−1) ≤ finrank`.
   *No rank-polynomial transfer needed at `def = 0`: `G_v` and `G` are both 0-dof and `Q_v` is realized at
   the SAME seed `q` that `Q` uses (no separate-seed transfer, unlike L7) — the `hold_span` is the direct
   subgraph membership. So L8 is SIMPLER than L7 (no V8/V8-a rank-polynomial sub-leaf).*
5. **`≤` from B2 + antisymmetry ⟹ rank `= D(|V|−1) − 0`.** `finrank_span_rigidityRows_add_deficiency_le`
   (B2, the free `≤`) at `def(G̃) = 0` gives `finrank ≤ D(|V|−1)`; antisymmetry closes the `HasGenericFullRankRealization`
   rank conjunct.
6. **GP / link-recording / alg-indep conjuncts.** GP (pairwise normal-LI): `Q_v`'s GP off `v` + the Π°
   normal making `v`'s pairs LI (the triple-LI ⟹ each pair LI). Link-recording: by selector construction.
   Alg-indep: same seed `q` (alg-indep extended at `v`). The extensor-nonzero conjunct (every `G`-link has
   nonzero supporting extensor): the `hne_G` discharge mirroring `case_II_realization_all_k:1088` — the two
   `v`-edges nonzero by the triple-LI (`panelSupportExtensor (Π°) (n_a) ≠ 0` etc.), the rest off the IH. □

*S/P/B note: Leaf 2 is **mostly mechanical assembly** of the L6 Case-II template — Brick A, B2, the seed
extension, the `hne_G` discharge are all landed patterns. The one genuinely-new geometric piece is **step 4's
`hnewpin`**: KT Lemma 5.3's "the two `v`-edge rows span rank `D` through `v`'s column" (a `D`-element
independent subfamily of the `2(D−1)` hinge rows). The two-LI-extensors-span-`D` fact is the Lemma-5.3 core;
`eq_of_hingeConstraint_two_parallel` (:2672) is the SAME-pair (`u,v` on both edges) form, but here the two
edges are `va` and `vb` (DISTINCT endpoints `a ≠ b`) sharing only `v` — so that lemma does NOT apply directly.
The needed fact is "two hinge rows at a common body `v`, with LI supporting extensors, are independent through
`v`'s column and together span the full `D`" — verify at build whether `finrank_hingeRowBlock` (`D−1` each) +
the LI-extensors + the `single v` projection assemble this, or whether a small new Lemma-5.3-at-distinct-
endpoints brick is needed (P≈3, the build-time uncertainty leaf — analogous to L7a). Steps 1–3, 5–6 are P≈2.*

**(e) The privacy fix (the one structural blocker, RESOLVED).** `linearIndependent_normals_of_algebraicIndependent`
is `private` in `CaseIII.lean:3407` (verified). Leaf 2 lives in `Theorem55.lean` (downstream of CaseIII in
the import chain `… ← CaseIII ← Theorem55`), so it cannot call a `private` CaseIII lemma. **Resolution:
de-privatize the bridge** — drop the `private` keyword on CaseIII:3407 (make it a public `lemma`/`theorem`).
It is a clean, general, reusable triple-LI fact (`AlgebraicIndependent ℚ q → 3 distinct vertices →
LinearIndependent ℝ ![q(a,·),q(b,·),q(c,·)]`), not churn-prone internal infrastructure — exactly the kind of
fact the project keeps public. Its existing CaseIII caller (:3658) is unaffected. *(Alternatives rejected:
(i) placing Leaf 2 in CaseIII.lean separates it from the dispatch it wires into — Theorem55 is where
`case_I_dispatch`/`case_I_realization_all_k`/`case_I_realization_nonsimple` live, so the producer belongs
there; (ii) re-mirroring the bridge duplicates a 30-line det-polynomial proof. De-privatizing is the
minimal, clean fix.)* No `set_option backward.privateInPublic` needed (the bridge is a `lemma`, not in an
exposed body). Same-commit grep: the only `private` reference is the def + the :3658 call.

**(f) Ordered leaf list + dependencies.** *(L8a refined by (c′): step 1 of Leaf 1 now consumes the NEW
def-antitone brick + an induced saturation; the two landed L8a sub-leaves — `exists_maximal_isProperRigidSubgraph`,
`rigidContract_not_simple` — stand.)*
* **L8a-0 — the def-antitone brick** `deficiency_le_deficiency_of_le_vertexSet_eq` (Deficiency.lean). The
  (c′) loop-case fix's one new piece: `H ≤ H'` at equal vertex sets ⟹ `def(H'̃) ≤ def(H̃)`. **The next
  concrete commit** — a small `partitionDef`-monotone-in-crossing-count + `ciSup` lemma, no rigidity, no
  dependency on anything else L8 needs. Mints no node (a `\uses`-only brick).
* **L8a step 2 — the shared-`v` extraction** `exists_isLink_pair_of_rigidContract_not_simple`
  (Contraction.lean, **LANDED** beside `rigidContract_not_simple`). The P≈3 sub-step, now discharged:
  given `G.Simple` + `hHsat` (every `G`-edge inside `V(H)` lies in `E(H)` — the (c′) induced-saturation
  abstraction) + `¬(G/E(H)).Simple` at `r ∈ V(H)`, produces `v ∉ V(H)` with two distinct edges `eₐ, e_b`
  into `V(H)` (other ends `a ≠ b ∈ V(H)`). Loop disjunct vacuous by `hHsat`; parallel disjunct's
  shared-`v` read off the auxiliary `collapseTo_eq_imp_mem_of_ne` (`r ∈ V(H)` ⟹ `collapseTo` merges two
  distinct vertices only inside `V(H)`). Axiom-clean. No rigidity, no `induce` (the caller supplies
  `hHsat`).
* **L8a — Leaf 1, `exists_degree_two_removeVertex_of_no_simple_contraction`** (ReducibleVertex.lean or
  Contraction.lean). The NEW combinatorics. Consumes the landed L8a sub-leaves
  (`exists_maximal_isProperRigidSubgraph`, `rigidContract_not_simple`, **`exists_isLink_pair_of_rigidContract_not_simple`**) +
  L8a-0 + `edgeSet_induce` (the (c′) induced saturation). Pure graph theory, no rigidity, no dependency on
  L8b. Mints a green node (or folds into `lem:case-I-dispatch`'s proof `\uses`). *Remaining: the
  induced-saturation opener (1a/1b) + the `G''=G'+v+{e,f}` build (steps 3–5, `removeVertex_deficiency_ge`
  + maximality/minimality). The shared-`v` extraction (step 2) is landed; `hHsat` is fed from
  `edgeSet_induce`.*
* **L8b — the privacy fix** (CaseIII.lean): drop `private` on :3407. A trivial one-token edit; can ride in
  L8c's commit. (Listed separately because it is a CaseIII edit, not a Theorem55 one — but it is gating for
  L8c, not standalone.)
* **L8c — Leaf 2, `case_I_realization_h65`** (Theorem55.lean) + the wiring (drop `theorem_55_d3:516`'s `h65`
  carry, rewrite the `:555` lambda). Depends on L8a (the graph side) + L8b (the bridge). Restates
  `lem:case-I-dispatch` green (flip `\leanok` on statement + proof; reword the stale "22i" prose to 22k);
  drops `h65` from any blueprint pin that states the carry. **Statement-grep gate** before commit: grep
  `blueprint/src` for `case_I_dispatch` / `theorem_55_d3` (the `lem:case-I-dispatch` `\lean{}` is
  `case_I_dispatch`, which is *unchanged*; `theorem_55_d3`'s `h65` carry-drop is a statement change — grep
  per `CLAUDE.md` *Structural-edit phases*). The P≈3 step-4 `hnewpin` Lemma-5.3-at-distinct-endpoints brick
  resolves at this build.

If the full pin won't fit one sitting: **L8a alone is a clean stopping point** (the new combinatorics +
its node green; `theorem_55_d3` still carries `h65`). L8c (the producer + wiring) is then a separate sitting.
The `case_I_dispatch:1867` all-`k` `h65` is **L9's** to drop (the spine wiring); L8 only discharges
`theorem_55_d3:516`'s carry.

**(g) Brick-by-brick load-bearing confirmation (clause (i)).** Every fact opened to its landed `def`/`theorem`:
* `removeVertex_deficiency_ge` (SplitOffDeficiency:405) — KT Lemma 4.4, **exact direction** `def(G̃) ≤
  def(G̃−v)`. ✓ (The §1.54(a3)-era "audit Phase-20; none surfaced" is now superseded: it HAS landed, and at
  the direction Claim 6.6 needs — NOT the converse. Confirmed step-by-step in (c) step 3.)
* `le_finrank_span_rigidityRows_of_pinned_placement` (RigidityMatrix:3344, **Brick A**) — span-level pin-a-body
  rank addition; conclusion `Nat.card ιn + Nat.card ιo ≤ finrank(span F.rigidityRows)`. ✓ (The KT (6.10)
  block-triangular workhorse; the `_augment` `+1` variant at :3390 is NOT needed — Claim 6.6 has no redundant
  `+1` row, unlike Case III stratum-1.)
* `case_II_realization_all_k` (CaseII:297) — the template: Brick A at :1063 + `exists_rankPolynomial_of_le_finrank_linking`
  + `hne_G` at :1088. ✓ L8 mirrors all but the rank-polynomial step (not needed at same-seed `def=0`).
* `linearIndependent_normals_of_algebraicIndependent` (CaseIII:3407) — triple-LI bridge, `private`. ✓ shape
  matches `(a,b,c) := (v,a,b)`; privacy resolved in (e).
* `eq_of_hingeConstraint_two_parallel` (RigidityMatrix:2672) — SAME-pair (`u,v` on both edges) Lemma-5.3 form.
  ✓ exists, **but flagged in (d) step 4**: NOT directly the distinct-endpoint Π° shape; the needed `hnewpin`
  fact is the two-hinges-at-common-body span-`D` form (P≈3, build-time).
* `finrank_hingeRowBlock` (:1129, each block `D−1`), `screwSpace_finrank` (:98, `= D`) — the rank arithmetic
  pieces for step 4. ✓
* `splitOff_removeVertex_minimalKDof` (ForestSurgery:3198) — `G−v` minimal `k'`-dof, `0 ≤ k' ≤ D−2`; in
  Claim 6.6 `k' = 0` (since `G−v = G'` rigid). ✓ Available but **not directly needed** — Leaf 1 establishes
  `G−v` minimal 0-dof via the maximal-subgraph identity `G−v = G'`, which is *stronger* (`k'=0`, not `≤ D−2`).
* `exists_adjacent_degree_two_pair` (ReducibleVertex:828) — KT Lemma **4.6**, adjacent degree-2 *pair*. ✓
  exists, **but NOT Claim 6.6's `v`**: Claim 6.6's degree-2 `v` comes from the maximal-subgraph construction
  (Leaf 1), not from Lemma 4.6. Flag: do not confuse the two — Lemma 4.6 feeds Case II/III splitting, not
  the Lemma-6.5 arm.
* `IsProperRigidSubgraph` (Deficiency:428) / `.vertexSet_nonempty` (:433) / `subgraph_minimality` (KT 3.3)
  / `simple_of_isMinimalKDof_of_noRigid` (ReducibleVertex:625) / `removeVertex_le` (Operations:553) /
  `Simple.mono` — the graph-side bookkeeping. ✓ all landed.
* `HasGenericFullRankRealization` (PanelHinge:1035) — the conclusion of both `h65` shapes and the IH `.1`
  conjunct; carries the rank-equality + GP + link-recording + alg-indep conjuncts L8 produces. ✓

**(h) Clause (ii) verdict — what's flagged, what's open.** NO motive/IH change (L8 reuses the §1.56 all-`k`
`Pc` IH unchanged; the `theorem_55_d3` `h65` discharge uses only the `k=0` IH). NO user adjudication: the
two `h65` shapes reconcile to one producer (the `k=0` derivation is internal, forced by Claim 6.6), and the
privacy issue resolves to a clean de-privatization. The **loop-case gap** the L8a-step-2 build surfaced is
**SETTLED in (c′)** — route through the induced saturation `G' := G.induce V(G₀)`, which makes the loop
disjunct vacuous; matches KT (= KT's silent edge-saturation of the maximal `G'`), no definitional change.
**Genuinely-new lemmas: ONE new brick + two flagged build-time leaves**, all buildable-from-landed-parts,
not research-shaped:
* *L8a-0, the def-antitone brick* `deficiency_le_deficiency_of_le_vertexSet_eq` (P≈2, NEW — (c′)): `H ≤ H'`
  at equal vertex sets ⟹ `def(H'̃) ≤ def(H̃)`; the loop-case fix's one new piece, lands first.
* *Leaf 1 step 2* (parallel-disjunct ⟹ shared-`v` extraction, P≈3) — the fiddly graph unpacking of
  `rigidContract`'s collapse; bounded. The loop disjunct is now discharged by `edgeSet_induce` (vacuous on
  the induced `G'`), so step 2 handles only the parallel mode.
* *Leaf 2 step 4* (the Lemma-5.3-at-distinct-endpoints `hnewpin` brick, P≈3) — two hinge rows at a common
  body `v` with LI extensors spanning the full `D` through `v`'s column; the `eq_of_hingeConstraint_two_parallel`
  same-pair form does not apply, so this is either a clean assembly of `finrank_hingeRowBlock` + the LI
  extensors or a small new brick (the build-time uncertainty leaf, L8's analogue of L7a/V8-a).
The honest residual: **Leaf 2 step 2's "G_v is 0-dof"** rests on Leaf 1's `G−v = G'` (the induced maximal
subgraph), which makes the `k=0`-only IH suffice — IF Leaf 1's step-2 extraction is harder than expected (the
P≈3 flag), Leaf 2's structure is unaffected (it consumes Leaf 1's conclusion as a black box). No open
decision for the coordinator/user.

**Estimate: ~3–4 commits** (L8a graph side ~1–2; L8c producer + wiring ~1–2; L8b privacy folds in). L8 is
**simpler than L7** (no rank-polynomial transfer — same-seed `def=0`) but carries **more new combinatorics**
(the maximal-subgraph existence + contraction-non-simplicity unpacking, which L7 had landed in
`splitOff_removeVertex_minimalKDof`).

### 1.70(i) The L8c geometric-core pin — the Leaf-2 step-4 `hnewpin` brick (RE-RATED to a pinned NEW brick) + the `case_I_realization_h65` exact Brick-A assembly (DESIGN-SETTLE, 2026-06-15, opus, docs-only)

The (d)/(h) "build-time uncertainty leaf" (step-4 `hnewpin`: clean assembly OR small brick — TBD at build)
is now **settled to a pinned NEW brick** with an exact route, and the producer's Brick-A instantiation is
pinned against Brick A's ACTUAL signature. Every load-bearing decl opened to its `theorem`/`def` body this
pass (clause (i)), and the two mathlib tools verified by loogle. **Net verdict (clause (ii)): no motive/IH
change, no user adjudication; one honest flag** (the OLD-block seed-restriction step, named in (i.2) below).
**The §1.70(d)-step-4 framing "the `eq_of_hingeConstraint_two_parallel` SAME-pair form does not apply, so
either a clean assembly or a small new brick" RESOLVES to: a small NEW brick, route fully pinned — re-rate
from "build-time uncertainty" to **buildable, P≈3.5**.**

**Finding 0 — the structural template is `case_II_realization_all_k` (CaseII:297), NOT `case_I_realization_all_k`.**
Verified: `case_I_realization_all_k` (Theorem55:1769) assembles its two legs through the HIGH-level coupler
`hasGenericFullRankRealization_of_couple_blockTriangular_ofNormals_set_kdof` (Theorem55:1850) — it does **not**
call Brick A directly. The decl that consumes Brick A is `case_II_realization_all_k` (Brick A at CaseII:1063).
So §1.70(d)'s "the L6 Case-II template widened" is the right reading: `case_I_realization_h65` mirrors
**`case_II_realization_all_k`'s geometric core (CaseII:937–1069)**, not the Case-I producer it sits beside.

**(i.1) The step-4 `hnewpin` brick — PINNED (genuinely new; no single landed lemma assembles it).** The need:
Brick A's `hnewpin : LinearIndependent ℝ (fun i : ιn => (rn i).comp (single ℝ _ v))` with `Nat.card ιn = D`
(`screwSpace_finrank:98`, `= screwDim 2 = 6`). L6 fills its `ιn` from a SINGLE edge `e_b` via
`linearIndependent_panelRow_comp_single_of_edge` (Pinning:503, the `D−1` block). L8's NEW block is the TWO
`v`-edges `va, vb` and must reach the FULL `D`. The per-edge tools each give only `D−1`:
* `exists_independent_panelRow_subfamily_of_edge` (Pinning:442) — `D−1` independent panel rows for one edge;
* `linearIndependent_panelRow_comp_single_of_edge` (Pinning:503) — those, pinned at `(ends e).1`, stay LI;
* `span_panelRow_comp_single_of_edge` (Pinning:547) — those pinned rows **span** `F.hingeRowBlock e = (span C(e))^⊥`.

So the pinned `va`-block spans `hingeRowBlock e_a` and the pinned `vb`-block spans `hingeRowBlock e_b`, each
`finrank D−1` (`finrank_hingeRowBlock:1129`). **The combined span is `hingeRowBlock e_a ⊔ hingeRowBlock e_b`,
and it has finrank exactly `D` iff the two supporting extensors are LI** — NOT a single landed lemma. Route
(all parts verified present):
* `finrank(U ⊔ W) = finrank U + finrank W − finrank(U ⊓ W)` via `Submodule.finrank_sup_add_finrank_inf_eq`
  (mathlib `FiniteDimensional/Lemmas:53`, verified by loogle).
* `U ⊓ W = (span C_a)^⊥ ⊓ (span C_b)^⊥ = (span C_a ⊔ span C_b)^⊥` via `Submodule.dualAnnihilator_sup_eq`
  (mathlib `Dual/Defs`, **the AVAILABLE direction** — `(U⊔V)^⊥ = U^⊥⊓V^⊥`; verified) + `hingeRowBlock_apply:807`
  (`hingeRowBlock e = (span {C(e)}).dualAnnihilator`). **Route note (coordinator correction 2026-06-15):**
  the pinned route uses `dualAnnihilator_sup_eq` (the `(U⊔V)^⊥ = U^⊥⊓V^⊥` direction) on `span C_a ⊔ span C_b`,
  which yields the inf-of-annihilators `U ⊓ W` directly — this is the cleanest tool and what the finrank
  chain needs. *(The recon claimed the reverse `(U⊓V)^⊥ = U^⊥⊔V^⊥` is "not in mathlib"; that holds only for
  general modules — `Submodule.sup_dualAnnihilator_le_inf` is `≤`-only — but for **field subspaces** (our
  ℝ-setting) the full reverse equality IS available as `Subspace.dualAnnihilator_inf_eq`, Dual/Lemmas.lean:860.
  It is not needed here: applying it would compute `(span C_a ⊓ span C_b)^⊥`, not the `U ⊓ W` we want, so
  `dualAnnihilator_sup_eq` stays the right tool. The error was a harmless non-load-bearing aside — the route
  is unaffected.)*
* `finrank(span C_a ⊔ span C_b) = 2` (two LI extensors) ⟹ `finrank((span C_a ⊔ span C_b)^⊥) = D − 2` via
  `Subspace.finrank_add_finrank_dualAnnihilator_eq` (mathlib `Dual/Lemmas:539`, the lemma `finrank_hingeRowBlock`
  already uses). So `finrank(U ⊔ W) = (D−1)+(D−1)−(D−2) = D`.
* Extract a `Fin D`-indexed LI subfamily of the union of pinned rows via `Submodule.exists_fun_fin_finrank_span_eq`
  (mathlib `Dimension/StrongRankCondition:651`, verified — same tool `exists_independent_panelRow_subfamily_of_edge`
  uses at Pinning:456). Each extracted row lies in the SET of pinned `(panelRow ends i).comp(single v)` rows of
  the two `v`-edges, so its un-pinned `panelRow ends i` is a member of `span F.rigidityRows` (`hnew_span`,
  via `panelRow_mem_rigidityRows`). **Brick-fit subtlety to discharge at build:** Brick A wants `rn : ιn → Dual`
  with `hnewpin : LI (rn · ∘ single v)`. `exists_fun_fin_finrank_span_eq` hands the PINNED rows directly; the
  `rn` are the un-pinned panel rows of the chosen `(edge, ⋀²-pair)` indices, and `hnewpin` is exactly the
  extracted LI. So the brick should conclude in the Brick-A-ready shape — return `ιn`, `rn`, `hnewpin`,
  `hnew_span` together. **Pin (lives in `RigidityMatrix.lean`, beside `linearIndependent_panelRow_comp_single_of_edge`
  / the pinned-placement bricks; name indicative):**
```lean
-- Two v-edges va, vb with LI supporting extensors: their hinge rows, pinned through v's screw column,
-- contain a D-element LI subfamily spanning the full D (KT Lemma 5.3, distinct-endpoint form).
theorem BodyHingeFramework.exists_independent_pinned_two_edge_span_full [DecidableEq α]
    (F : BodyHingeFramework k α β) {ends : β → α × α} {v a b : α} {eₐ e_b : β}
    (hva : (ends eₐ) = (v, a)) (hvb : (ends e_b) = (v, b))   -- producer FORCES this orientation, see (i.2)
    (haₐ : a ≠ v) (hbb : b ≠ v)
    (hne_a : F.supportExtensor eₐ ≠ 0) (hne_b : F.supportExtensor e_b ≠ 0)
    (hgen : LinearIndependent ℝ ![F.supportExtensor eₐ, F.supportExtensor e_b]) :
    ∃ (ιn : Type) (_ : Fintype ιn) (rn : ιn → Module.Dual ℝ (α → ScrewSpace k)),
      Nat.card ιn = screwDim k ∧
      LinearIndependent ℝ
        (fun i : ιn => (rn i).comp (LinearMap.single ℝ (fun _ : α => ScrewSpace k) v)) ∧
      (∀ i : ιn, rn i ∈ Submodule.span ℝ F.rigidityRows)
```
*S/P/B:* genuinely new, but every sub-fact is landed/mathlib — **P≈3.5, buildable, not research-shaped.** The
`Fin D` ⟹ `Nat.card ιn = D` and the unpinning are bookkeeping; the mathematical content is the `finrank = D`
chain above. **NOTE the orientation hypotheses** `(ends eₐ) = (v,a)`, `(ends e_b) = (v,b)` — the producer
supplies them by *construction* (see (i.2)), so the brick avoids L6's `hnewpin_eb` swap gymnastics
(CaseII:983–1035, the `(ends e_b) = (b,v)` reorientation) entirely.

**The two-LI-extensors hypothesis `hgen` is supplied, not assumed.** `C(va) = panelSupportExtensor(q(v,·),q(a,·))`,
`C(vb) = panelSupportExtensor(q(v,·),q(b,·))`. From the triple-LI `![q(v,·),q(a,·),q(b,·)]` (the de-privatized
L8b bridge `linearIndependent_normals_of_algebraicIndependent` at `(a,b,c):=(v,a,b)`), the two joins
`join(n_v,n_a)`, `join(n_v,n_b)` are LI in `⋀²` — established via `panelSupportExtensor_linearIndependent_iff`
(PanelLayer:810, `LI panelSupportExtensor ↔ LI normalsJoin`). This is the geometric heart "two edges through a
common body, non-collinear normals ⟹ independent extensors"; it is what KT Lemma 5.3 needs in the distinct-
endpoint form, and it is the only place L8b's triple-LI bridge enters the geometric side.

**(i.2) The producer `case_I_realization_h65` — exact assembly route, pinned against Brick A's actual signature.**
Brick A (`le_finrank_span_rigidityRows_of_pinned_placement`, RigidityMatrix:3344, **verbatim** this pass):
takes `(F : BodyHingeFramework k α β) {v} {rn : ιn → Dual} {ro : ιo → Dual}`, hypotheses
`hold : ∀ j x, ro j (update 0 v x) = 0`, `hnewpin : LI (rn · ∘ single v)`, `holdindep : LI ro`,
`hnew_span : ∀ i, rn i ∈ span F.rigidityRows`, `hold_span : ∀ j, ro j ∈ span F.rigidityRows`; concludes
`Nat.card ιn + Nat.card ιo ≤ finrank (span F.rigidityRows)`. The producer instantiates it as the L6 template
(CaseII:1036–1069) with `ιn` = the (i.1) brick's `D`-element NEW index and `ιo` = the IH's `G_v`-row OLD index.
The body (matches `theorem_55_d3:516`'s `h65` carry exactly — re-verified: hyps `hD hn hfresh G hG hV3 hrig
hSimple hnoSimpleContr hIH`, conclusion `HasGenericFullRankRealization 2 n G`, §1.70(d) pin unchanged):

1. **Graph side (Leaf 1, L8a, LANDED).** `exists_degree_two_removeVertex_of_no_simple_contraction` → `v, a, b,
   eₐ, e_b`; `v` degree-2; `G_v := G.removeVertex v` minimal 0-dof + simple; `a ≠ b`, `a,b ≠ v`, `eₐ ≠ e_b`.
2. **IH at `G_v` (`k=0` arm).** `(hIH G_v hG_v hV_v hlt).1 hG_v.Simple : HasGenericFullRankRealization 2 n G_v`
   → `Q_v`, GP, rank `= D(|V_v|−1)` (`def=0`), link-recording, **alg-indep seed `q := fun p => Q_v.normal p.1 p.2`**
   (the `HasGenericFullRankRealization` motive's five conjuncts, PanelHinge:1035 verified). `G_v` is 0-dof, so
   the `k=0`-only IH suffices — the L8-not-all-`k` finding.
3. **Build `Q := ofNormals G ends q'` on the extended seed.** `q'` = `q` extended at `v` by a fresh Π° normal
   (the §1.53 free-normal extension keeping alg-indep + pairwise-LI; `v`'s normal makes `![q'(v,·),q'(a,·),
   q'(b,·)]` triple-LI). **`ends` is CHOSEN so `ends eₐ = (v,a)`, `ends e_b = (v,b)`** (first endpoint `v` on
   both `v`-edges; off the two, `ends = G.endsOf`/the IH's selector) — this is what feeds (i.1)'s orientation
   hyps and removes L6's swap branch. `Q.graph = G` (`ofNormals_graph`); link-recording via
   `ofNormals_recordsLinks_of_hends` (PanelHinge:1057).
4. **Rank `≥ D(|V|−1)` via Brick A.** NEW block `(ιn, rn)` from (i.1)'s brick (`hnewpin` + `hnew_span` +
   `Nat.card ιn = D`); OLD block `(ιo, ro)` = `Q_v`'s `D(|V_v|−1)` panel rows. Discharges:
   * `holdindep` — the IH realization's rows are independent (from `Q_v`'s rank-`D(|V_v|−1)` realization, the
     `exists_independent_*` family the IH carries; same as L6's `hso_indep`).
   * `hold : ∀ j x, ro j (update 0 v x) = 0` — every OLD row is an `eᵢ`-hinge at a `G_v`-link, whose endpoints
     are in `V(G_v)` and so `≠ v` (`v ∉ V(G_v)`); `hingeRow … (update 0 v x) = annih(0−0) = 0`. EXACTLY L6's
     `hold` (CaseII:963–977) — `Q_v`-rows avoid `v`.
   * `hold_span : ∀ j, ro j ∈ span Q.toBodyHinge.rigidityRows` — **the genuinely-simpler-than-L6 step.** L6's
     OLD block came from a SPLIT-OFF `Gab = G.splitOff v a b e₀` (CaseII `hso_span`, 70 lines, the extensor-
     agreement-up-to-swap argument at :827–895). Here `G_v ≤ G` is a GENUINE subgraph (`removeVertex_le`) and
     `Q` is built on the SAME seed `q'` whose restriction to `V(G_v)` IS `q` (the `ofNormals`-same-seed identity).
     So each `G_v`-link is a `G`-link with the IDENTICAL supporting extensor, and `ro j = Q_v.panelRow …` is
     LITERALLY a `Q.panelRow …` ⟹ `∈ span Q.rigidityRows` by `Submodule.subset_span ∘ panelRow_mem_rigidityRows`
     (the §1.68(d) TRIVIAL `Gv ≤ G` case). **Honest flag (the one named step, not a blocker):** this needs the
     *seed-restriction* fact "`Q`'s normals on `V(G_v)` = `Q_v`'s normals" — mechanically true by the
     extended-seed construction (`q'` agrees with `q` off `v`, and `G_v`-vertices are `≠ v`), but the build must
     state it (a `funext` + `Function.update_of_ne`); it is the one place where "extend the seed at `v`" has a
     proof obligation. P≈2, no design risk.
   * `hnew_span` — (i.1) returns it.
   `le_finrank_span_rigidityRows_of_pinned_placement Q.toBodyHinge (v:=v) hold hnewpin holdindep hnew_span
   hold_span : D + D(|V_v|−1) ≤ finrank`, i.e. `D(|V|−1) ≤ finrank` (`|V_v| = |V|−1`, `vertexSet_removeVertex`
   + `ncard_diff_singleton`). **No rank-polynomial transfer** (unlike L6/L7): same-seed, both 0-dof.
5. **`≤` + antisymmetry ⟹ rank `= D(|V|−1) − 0`.** `finrank_span_rigidityRows_add_deficiency_le` (B2) at
   `def(G̃)=0` (`hG.1`) gives `finrank ≤ D(|V|−1)`; antisymmetry closes the rank conjunct.
6. **GP / link-recording / alg-indep / extensor-nonzero conjuncts.** GP (pairwise normal-LI): `Q_v`'s GP off
   `v` + the Π° normal making `v`'s pairs LI (triple-LI ⟹ each pair LI). Link-recording: step 3. Alg-indep:
   the extended seed `q'`. Extensor-nonzero (every `G`-link has nonzero supporting extensor): mirrors
   `case_II_realization_all_k:1088` `hne_G` — the two `v`-edges nonzero by `panelSupportExtensor_ne_zero_iff`
   on the triple-LI, the rest off the IH.

**Steps 1–3, 5–6 COMPOSE (confirmed against the L6 template).** Steps 1–2 are the landed Leaf-1 + the
`HasGenericFullRankRealization` destructure; step 3 is the `ofNormals` + chosen-`ends` build (the seed-extension
is the §1.53 landed idiom); step 5 is one B2 call + `le_antisymm`; step 6 mirrors L6's conjunct discharges
verbatim. The only NEW Lean content beyond assembly is the (i.1) `hnewpin` brick and the (i.2) step-4
`hold_span` seed-restriction `funext` (P≈2). **No step fails to compose; no motive/IH change; no user decision.**

**(i.3) Resulting buildable leaf sequence (the L8c slice, exact signatures).**
* **L8c-1 — the `hnewpin` brick** `BodyHingeFramework.exists_independent_pinned_two_edge_span_full`
  — **LANDED (2026-06-15).** **Two pin corrections forced by landed source (no math change):** the file
  is **`Pinning.lean`** (beside `span_panelRow_comp_single_of_edge`), NOT `RigidityMatrix.lean` — the
  brick consumes `panelRow`/the per-edge tools (`exists_independent_panelRow_subfamily_of_edge`,
  `span_panelRow_comp_single_of_edge`), all of which are downstream of `RigidityMatrix` (Pinning ←
  PanelLayer ← RigidityMatrix), so `RigidityMatrix.lean` placement is a circular import. And the
  signature gains two link hyps `hlink_a : F.graph.IsLink eₐ v a`, `hlink_b : F.graph.IsLink e_b v b`
  (the (i.1) pin omitted them — `hnew_span`'s `panelRow_mem_rigidityRows` needs the link; the L8c-2
  producer supplies them by construction via `ofNormals_recordsLinks`). Self-contained
  finrank/dual-annihilator + extract-LI; no `ofNormals`/producer dependency. Mints no node (a
  `\uses`-only brick).
* **L8c-2 — the producer** `PanelHingeFramework.case_I_realization_h65` (Theorem55.lean, signature §1.70(d)
  UNCHANGED) + L8b privacy fix (drop `private` on CaseIII:3407, folds in) + wiring (rewrite
  `theorem_55_d3`'s `:555` lambda to call the producer, drop the `h65` signature carry at :516–:524). Restates
  `lem:case-I-dispatch` green (flip `\leanok` on statement + proof; reword the stale "obligation of sub-phase
  22i" prose to 22k). **Statement-grep gate:** `theorem_55_d3`'s `h65` carry-drop is a statement change — grep
  `blueprint/src` for `theorem_55_d3` per the `CLAUDE.md` *Structural-edit phases* per-slice gate.

### 1.71 The L10 signature pin — Theorem 5.6 at `d = 3` (the `def > 0` `prop:rigidity-matrix-prop11` feed): **V9 RESOLVED FREE** (the homogeneous projective move is already landed as `exists_extensor_in_two_panels`), the deficiency-preserving spanning-strip is a NEW greedy edge-deletion brick (verified absent in tree), the `def > 0` `hgen` feed assembles strip → `theorem_55_all_k` (after `subgraph_minimality`) → `withGraph` re-add (`finrank_infinitesimalMotions_le_of_graph_le`, landed) → `rigidityMatrix_prop11`; sliced L10a–L10d (2026-06-16, opus, docs-only)

> **STATUS (2026-06-16, post-L10a/L10b/L10c — only L10d remains).** Flag (i) DISSOLVED (L10a:
> the strip brick `exists_isMinimalKDof_spanning_subgraph` landed via a finite minimum over
> deficiency-preserving edge subsets — no separate no-deletable-edge⟺`IsMinimalKDof` micro-pin).
> Flag (ii) RESOLVED FREE (L10b: `theorem_55_minimalKDof_k` landed — the general-`k` re-expose,
> same callback map as `theorem_55_all_k`, only `0 G hG`→`k G hG`). **So (c) step 2 below now uses
> `theorem_55_minimalKDof_k`, NOT `theorem_55_all_k`** — the step-2 "FLAG: needs `IsMinimalKDof n 0`"
> is closed. L10c (the §1.71(c) producer `rankHypothesis_of_theorem_55_d3`) is the next build; its
> `hgen` comes from `withGraph` monotonicity (step 4), not from "Brick A". **L10c LANDED** (the
> §1.71(c) producer `rankHypothesis_of_theorem_55_d3` + the `reaimSub` micro-bricks, salvaged +
> warning-clean). **L10d LANDED + 22k CLOSED (2026-06-16):** `prop:rigidity-matrix-prop11` flipped
> red→green, `thm:theorem-55-6-d3` minted (pinned to the L10c `def>0` + 22h `def=0` feeds); the
> prop↔Thm-5.6 dep edge runs one-way (Thm-5.6 proof `\uses` the prop) to keep the dep-graph acyclic.
> KT Thm 5.5 + Thm 5.6 are formalized at `d = 3`. Next: Phase 23 (general `d`, KT Lemma 6.13).

> **Docs-only design pass (the L10 build-out).** Lean re-read this pass against the LANDED source
> (the actual `def`/`theorem`/API, not the prior prose's optimism, per the mandatory clause (i)):
> RigidityMatrix.lean — `BodyHingeFramework` (`:685`, `supportExtensor : β → ScrewSpace k` a field),
> `infinitesimalMotions` (`:1012`, quantifies links only), `IsInfinitesimallyRigidOn` (`:2530`),
> `span_rigidityRows_eq_dualAnnihilator_infinitesimalMotions` (`:1073`), `finrank_screwAssignment`
> (`:2641`); Pinning.lean — `withGraph` (`:922`), `infinitesimalMotions_le_withGraph_of_le` (`:1010`),
> `finrank_infinitesimalMotions_le_of_graph_le` (`:1038`), `RankHypothesis` (`:738`); PanelHinge.lean —
> `HasPanelRealization` (`:1090`), `rigidityMatrix_prop11` (`:1136`); Theorem55.lean — `theorem_55_all_k`
> (`:2126`), `theorem_55_d3` (`:2201`), `rankHypothesis_deficiency_of_theorem_55_d3` (`:804`),
> `reaim` (`:772`); Deficiency.lean — `IsKDof`/`IsMinimalKDof` (`:350`/`:359`), `subgraph_minimality`
> (`:684`, KT 3.3), `rank_add_deficiency_eq` (`:2080`), `deficiency_le_deficiency_of_le_vertexSet_eq`
> (`:751`); PanelLayer.lean — `exists_extensor_in_two_panels` (`:631`), `panelSupportExtensor_ne_zero_iff`
> (`:242`), `extensorInPanel_panelSupportExtensor` (`:616`). Blueprint: `prop:rigidity-matrix-prop11`
> (panel-layer.tex:100, red — proof `\uses{thm:theorem-55,…}`), `lem:motions-mono-of-graph-le`
> (panel-layer.tex:600, GREEN, pinned to `infinitesimalMotions_le_withGraph_of_le` +
> `finrank_infinitesimalMotions_le_of_graph_le`), `thm:theorem-55-d3-instance` (`thm:theorem-55`
> region, green). KT pp. 668–671 (Thm 5.5/5.6 statements + Thm 5.6 proof) re-read this pass; the rank
> monotonicity (purpose 1) and the projective-move freeness (purpose 2) cross-checked against the landed
> homogeneous model. No `.lean`/`.tex` edits this pass.

**(a) V9 RESOLVED — the homogeneous projective move is FREE, and its enabling brick is already
landed.** KT's Thm 5.6 proof (p. 670, verbatim re-read) does the re-add in two logically separate
sub-steps, which the project's model separates cleanly:

* **Purpose 1 — the rank LOWER bound `rank R(G,p) ≥ rank R(G',q)`.** KT phrases this as "obvious"
  (more edges, rank cannot drop). In the project it is the **already-green**
  `lem:motions-mono-of-graph-le` = `finrank_infinitesimalMotions_le_of_graph_le` (`Pinning.lean:1038`):
  for `G' ≤ F.graph`, `finrank Z(F.graph) ≤ finrank Z(F.withGraph G')`. **This holds for ANY shared
  `supportExtensor` field** — `withGraph` re-adds edges keeping the *same* extensor data
  (`withGraph_supportExtensor`), and `infinitesimalMotions` only quantifies over *links*
  (`:1012`, `∀ e u v, IsLink → …`), so adding a link can only *add* a constraint and shrink `Z`.
  The lower bound is therefore free **regardless of whether the re-added edges' extensors are
  genuine** — KT's projective move is NOT needed for purpose 1 at all. (This is the one place the
  §1.56(e) prose was over-careful: it bundled the projective move into the lower bound; the landed
  `withGraph` monotonicity makes purpose 1 unconditional.)

* **Purpose 2 — the re-added framework is a *valid* (genuine-hinge) panel-hinge realization.** This
  is where KT actually uses projective invariance: he needs `Π_{G',q}(u) ∩ Π_{G',q}(v) ≠ ∅` for
  *every* pair `(u,v)`, so each re-added edge `uv ∉ E'` gets a genuine `(d−2)`-hinge `p(uv)` sitting
  in the panel intersection. In the **project's homogeneous model** panels are linear hyperplanes
  through the origin: `panel(v) = (normal v)^⊥ ⊆ ℝ^{k+2} = ℝ^{d+1}`. **Two linear hyperplanes through
  the origin in `ℝ^{d+1}` ALWAYS meet in a subspace of dimension `≥ (d+1) − 2 = d − 1`** (= the
  homogenization of a `(d−2)`-affine subspace) — *with no transversality hypothesis whatsoever*. The
  Lean brick is **already landed**: `exists_extensor_in_two_panels` (`PanelLayer.lean:631`) produces a
  nonzero `C : ScrewSpace 2` with `ExtensorInPanel C n₁ ∧ ExtensorInPanel C n₂` for **any** `n₁ n₂`,
  by rank–nullity on the pairing `x ↦ (x⬝n₁, x⬝n₂)` (kernel `n₁^⊥ ∩ n₂^⊥` has `dim ≥ 4 − 2 = 2`,
  giving the two spanning points) — its docstring says "regardless of whether `n₁` and `n₂` are
  linearly independent." This is *exactly* KT's projective move, made free by homogenization. The
  re-added edge's extensor need not be nonzero/transversal for the *rank* (purpose 1); when the bare
  motive `HasPanelRealization` (`:1090`) demands a genuine per-link `ExtensorInPanel` witness,
  `exists_extensor_in_two_panels` supplies it.

  **Verdict: V9 is FREE — no genuinely-new geometry.** The "two distinct hyperplanes meet" fact the
  §1.56(e) prose conjectured is not merely true in the homogeneous model; the producing lemma is
  *already in the tree* (it was built as the L4a cut-edge brick). One honest caveat to flag, not a
  blocker: KT's stated re-add gives the re-added panels a hinge in their *(possibly non-transversal)*
  intersection; the project's `exists_extensor_in_two_panels` likewise does not assume transversality,
  so the re-added edges may carry a *degenerate* (non-genuine, possibly even non-transversal) hinge
  when two normals happen to be proportional. This matches KT (whose `q` is generic on `E'` but says
  nothing about non-`E'` pairs) and is absorbed by the bare `HasPanelRealization` motive, which asks
  only `ExtensorInPanel` (membership), *not* `≠ 0` strengthened to transversality. **No `def:`-node
  reshape, no motive change, no IH change** (clause (ii): not triggered).

**(b) The deficiency-preserving spanning-strip brick — a NEW lemma (verified absent in tree).** Grep
confirmed there is no existing greedy-edge-deletion / minimal-`k`-dof spanning-subgraph extraction
(`exists.*IsMinimalKDof.*le`, `exists_spanning`, `deficiency-preserving`, etc. all empty). The landed
`subgraph_minimality` (`Deficiency.lean:684`, KT 3.3) is the *wrong direction* — it needs `G` *already*
minimal-`k`-dof. The strip starts from an *arbitrary* `G`. Exact signature (the genuinely-new
combinatorial leaf):

```lean
theorem Graph.exists_isMinimalKDof_spanning_subgraph [DecidableEq β] [Finite α] [Finite β]
    (G : Graph α β) (n : ℕ) (hD : 1 ≤ Graph.bodyBarDim n) (hne : V(G).Nonempty) :
    ∃ G' : Graph α β, G' ≤ G ∧ V(G') = V(G) ∧
      G'.IsMinimalKDof n (G.deficiency n)
```

**Route (verified buildable against the landed API).** Greedy edge deletion under matroid-rank
descent, NOT a bespoke `def`-recursion:

1. `def(G̃) = D(|V|−1) − rank M(G̃)` is the landed `rank_add_deficiency_eq` (`:2080`), so at fixed
   `V` (which `deleteEdges` preserves — `vertexSet_deleteEdges` keeps `V(G)`, mathlib
   `Graph/Delete.lean:39`), *`def` is invariant iff `rank M(G̃)` is invariant.*
2. Run `Nat.findGreatest`/well-founded recursion on `|E(G)|` (finite, `[Finite β]`): if some edge
   `e ∈ E(G)` has `rank M((G.deleteEdges {e})~) = rank M(G̃)`, delete it (`deleteEdges_le` keeps
   `G' ≤ G` and `V` fixed) and recurse; else stop. The measure strictly decreases on each deletion.
3. At the stopping point `G'`: `def(G̃') = def(G̃)` (rank preserved at every step, `V` fixed), and
   *no edge is deletable keeping the rank* — which is precisely the `IsMinimalKDof` base/fiber-meeting
   condition: minimality `∀ B base of M(G̃'), ∀ e ∈ E(G'), B ∩ ẽ ≠ ∅` is the matroid statement "every
   edge-fiber is rank-load-bearing," equivalent to "deleting `e` drops `rank M(G̃')`" via
   `isBase_ncard_add_deficiency_eq` (`:2091`) + the edge-fiber/restriction identity
   `matroidMG_restrict_mulTilde`.

**FLAG (clause (ii), a real open decision for the L10a build, NOT a blocker):** step 3's
"no-deletable-edge ⟺ `IsMinimalKDof`" equivalence is *stated* in the `IsMinimalKDof` docstring
("no edge of `G` can be deleted without lowering the rank of `M(G̃)`") but is **not** a landed lemma —
the `def` *unfolds* to a base/fiber-meeting condition, and converting "rank drops on deleting `e`" to
"every base meets `ẽ`" is a real (if standard) matroid argument over `matroidMG`/`edgeFiber`. I am
*confident in the SHAPE* (it is the contrapositive of `subgraph_minimality`'s engine, run at
`G'.deleteEdges {e} ≤ G'`), so it is buildable, but it is a **P≈3.5 matroid leaf, not a one-liner**;
its internal route (the cleanest is: `e` deletable keeping rank ⟹ some base `B` of `M(G̃')` avoids
`ẽ` ⟹ `B` is a base of `M((G'.deleteEdges{e})~)` of equal size ⟹ contradiction with `e`'s
fiber-meeting) should get its own micro-pin at the L10a build if it doesn't fall out of the existing
`matroidMG`/`isBase` API in one pass. **This is the one piece whose exact Lean shape I cannot pin with
full confidence from the design pass alone** — recorded honestly here for coordinator/user
adjudication per clause (ii); it does not change the motive or any signature, only the *cost* of L10a.

**(c) The `def > 0` `hgen` feed — end-to-end assembly (each named input is landed; each new leaf is
named).** The target is `prop:rigidity-matrix-prop11`'s genuine first `def > 0` feed. The shape
mirrors the landed `def = 0` feed `rankHypothesis_deficiency_of_theorem_55_d3` (`:804`) — confirmed
by reading its body — but at `def(G̃) = k > 0` the framework is *not* rigid, so the `hgen` upper
bound `(finrank Z : ℤ) ≤ screwDim k + def` comes from the strip's rank equality, not from rigidity.

The producer (the L10c deliverable):

```lean
theorem PanelHingeFramework.rankHypothesis_of_theorem_55_d3
    [Nonempty α] [Finite α] [Finite β] [DecidableEq β]
    (hfresh : ∀ G' : Graph α β, ∃ e₀ : β, e₀ ∉ E(G'))
    (G : Graph α β) (hne : V(G).Nonempty) (hspan : V(G) = Set.univ) (hSimple : G.Simple) :
    ∃ Q : PanelHingeFramework 2 α β, Q.graph = G ∧
      Q.toBodyHinge.RankHypothesis (G.deficiency 3)
```

**Assembly (every step traced; landed inputs named, new leaves named):**

1. **Strip.** `exists_isMinimalKDof_spanning_subgraph G 3 …` (L10a, NEW) → `G' ≤ G`, `V(G') = V(G)`,
   `G'.IsMinimalKDof 3 (G.deficiency 3)`. Spanning is automatic (`deleteEdges` fixes `V`).
2. **Realize the spanning subgraph.** `theorem_55_all_k` (`:2126`, LANDED) applied to `G'` with
   `k := G.deficiency 3` (= `G'.deficiency 3` by step 1) yields the GP conjunct
   `HasGenericFullRankRealization 2 3 G'` *when `G'.Simple`* — `G' ≤ G` simple ⟹ `G'.Simple`
   (`Simple.mono`). Destructure to a `Q' : PanelHingeFramework 2 α β` with `Q'.graph = G'` and the
   rank conjunct `(finrank span Q'.rigidityRows : ℤ) = D(|V(G')|−1) − def(G̃')`.
   *(`theorem_55_all_k` needs `hD : 6 ≤ bodyBarDim n`, `hn : bodyBarDim n = screwDim 2`, `hfresh`,
   `G'.IsMinimalKDof n 0`* — **wait: it needs `IsMinimalKDof n 0`, the 0-dof spine.** See FLAG below.)
3. **Re-add edges via `withGraph`.** Form `F := Q'.toBodyHinge.withGraph G` (LANDED `withGraph`,
   `:922`; same `supportExtensor`, graph now `G ⊇ G'`). For the *bare* `HasPanelRealization` motive,
   re-aim the `ends`/`normal` on non-`E(G')` links so each carries the
   `exists_extensor_in_two_panels` witness (V9, (a)); but for the `rigidityMatrix_prop11` `hgen` feed
   we need only the `finrank` bound, so this step is just `withGraph`.
4. **`hgen` from monotonicity.** `finrank_infinitesimalMotions_le_of_graph_le Q'.toBodyHinge (hle : G' ≤ G)`
   (`:1038`, LANDED `lem:motions-mono-of-graph-le`) gives
   `finrank Z(Q'.toBodyHinge.graph = G') ≥ finrank Z(F.graph = G)` …
   **— direction check (clause (i)):** the lemma reads `finrank Z(F.graph) ≤ finrank Z(F.withGraph G')`
   for `G' ≤ F.graph`, i.e. the *bigger* graph has the *smaller* `Z`. Here the bigger graph is `G`,
   so set `F := <a framework on G>` and `G' := <the spanning subgraph>`; `finrank Z(G) ≤ finrank Z(G')`.
   The strip's `Q'` realizes `G'` at rank `D(|V|−1) − k`, i.e. `finrank Z(G') = D + k` (via
   `span_rigidityRows_eq_dualAnnihilator_infinitesimalMotions` + `finrank_screwAssignment` at
   spanning, the `:1073`/`:2641` bridge). So `finrank Z(G) ≤ D + k = screwDim 2 + def(G̃)`, which IS
   `hgen`.
5. **`hC`.** Every edge's `supportExtensor ≠ 0`: for `E(G')` edges, GP on `Q'` (link-recording + GP
   + looplessness, exactly the `:850` `hC` block of the `def=0` feed); for re-added `E(G)∖E(G')`
   edges, the V9 brick gives a nonzero in-two-panels extensor (the `reaim`-style off-edge selector,
   `:772`, generalized to put `exists_extensor_in_two_panels`'s `C` on the re-added links). One
   micro-brick: a `withGraph`/`reaim` variant that installs the in-two-panels extensor on the new
   edges (P≈2, mirrors `reaim`).
6. **Conclude.** `rigidityMatrix_prop11 F 3 (by omega) hC hgen` (`:1136`, LANDED) →
   `F.RankHypothesis (F.graph.deficiency 3) = RankHypothesis (G.deficiency 3)`. ∎

**FLAG (clause (ii), the one genuine cross-cutting decision — surfaced, NOT forced):** step 2's
`theorem_55_all_k` produces a realization of the *minimal-`k`-dof* `G'` at *its own* deficiency
`k = def(G̃')`. That is exactly KT's Thm 5.5 *at `k = def`* — and the §1.54(b)/§1.56(e) prose has
always said this is the all-`k` content. **The L9 spine `theorem_55_all_k` ALREADY delivers all-`k`**
(its `hG : G.IsMinimalKDof n 0` hypothesis is the *0-dof* spine — but the *induction inside it* runs
over all `k`, and its conclusion at a `k`-dof `G'` comes from instantiating the all-`k` reduction).
**Re-reading `theorem_55_all_k` (`:2129`): its hypothesis is `hG : G.IsMinimalKDof n 0`, the 0-dof
form.** So as landed it realizes only *0-dof* minimal graphs — it does NOT directly realize a
`k`-dof `G'` for `k > 0`. The strip lands a `k`-dof `G'` with `k = def(G̃) > 0`; **`theorem_55_all_k`
cannot be applied to it directly.**

This is the load-bearing finding of the L10 design pass, and it is the point to STOP and adjudicate:

> **The `def > 0` Thm 5.6 feed needs Theorem 5.5 stated at a `k`-dof minimal graph for `k > 0`, but
> the landed `theorem_55_all_k` concludes only for `k = 0`-dof minimal graphs.** The all-`k`
> *induction* is inside the proof (Case III applies the IH at a `k'`-dof nested graph), but the
> *exposed theorem* is `IsMinimalKDof n 0`. To feed Thm 5.6 at `def > 0`, the spine must be re-exposed
> at `IsMinimalKDof n k` (general `k`), OR a thin all-`k` wrapper `theorem_55_minimalKDof_k` must be
> extracted from the same `minimal_kdof_reduction_all_k` call with the `0 G hG` final argument
> generalized to `k G hG`.

**Which it is — a one-line re-expose or a real gap — I cannot pin with full confidence from the
design pass**, because it turns on whether `minimal_kdof_reduction_all_k` (the §1.59 principle) is
genuinely stated for all `k` (in which case the `theorem_55_all_k` body's `0 G hG …` tail just
generalizes to `k G hG …`, a near-free wrapper) or only instantiated at `k=0` in a way that the
producers (`theorem_55_base_producer`, `case_*_realization_all_k`, `case_III_realization`) silently
assume `k=0` somewhere. The producers are *named* all-`k` (`case_II_realization_all_k`,
`case_I_realization_all_k`) and the carries table says the all-`k` IH is threaded — which strongly
suggests the wrapper is near-free — but **confirming it is an L10b build-time check against the actual
`minimal_kdof_reduction_all_k` signature + the producers' `k`-quantification, not a design-pass
certainty.** Per clause (ii), I am flagging this rather than asserting "the wrapper is free": if a
producer turns out to assume `k=0` (e.g. a rigidity-gated step that the deficient form can't supply),
the L10 estimate changes and the gap needs its own pin. **This is the first thing L10b must settle.**

**(d) The L10 sub-layer plan (ordered buildable leaves; exact signatures + P-rough-rating).**

* **L10a — the spanning-strip brick** `Graph.exists_isMinimalKDof_spanning_subgraph` (signature in
  (b); `Deficiency.lean`, beside `subgraph_minimality`). **P≈3.5** (the no-deletable-edge ⟺
  `IsMinimalKDof` matroid step is the cost; the greedy WF recursion + `vertexSet_deleteEdges` are
  mechanical). Pure addition; mints no node (a `\uses`-only brick for the prop11 proof). **Gated on
  the (b) FLAG only if the matroid step needs a user call; otherwise self-contained.**
* **L10b — the all-`k` minimal-graph spine re-expose** `theorem_55_minimalKDof_k` (or a generalization
  of `theorem_55_all_k`'s final-argument): conclude `(G.Simple → HasGenericFullRankRealization 2 n G)
  ∧ HasPanelRealization 2 n G` from `G.IsMinimalKDof n k` for *general* `k` (drop the `0`).
  **P≈1 if the wrapper is free (the (c) FLAG resolves favorably); P≈?? if a producer assumes k=0**
  — *this layer's first task is to settle the (c) FLAG against the landed `minimal_kdof_reduction_all_k`
  + producer signatures.* No new node (re-pin `thm:theorem-55` / `thm:theorem-55-d3-instance` prose if
  the exposed shape changes; statement-grep gate on `theorem_55_all_k`).
* **L10c — the `def > 0` prop11 producer** `PanelHingeFramework.rankHypothesis_of_theorem_55_d3`
  (signature in (c); Theorem55.lean tail, beside `rankHypothesis_deficiency_of_theorem_55_d3`).
  **P≈3** (the assembly is the (c) 6-step chain — strip ∘ L10b ∘ `withGraph` ∘ monotonicity ∘
  prop11; the one micro-brick is the (c) step-5 in-two-panels off-edge selector, P≈2, a `reaim`
  variant). Consumes `exists_isMinimalKDof_spanning_subgraph` (L10a), `theorem_55_minimalKDof_k`
  (L10b), `finrank_infinitesimalMotions_le_of_graph_le` + `withGraph` + `rigidityMatrix_prop11` +
  `exists_extensor_in_two_panels` (all landed).
* **L10d — the blueprint flip** (one docs+TeX commit, after the Lean lands). Target nodes (PLAN, not
  flipped this pass):
  - **`prop:rigidity-matrix-prop11`** (panel-layer.tex:100, red → green): drop the proof's
    `\uses{thm:theorem-55,…}` *as the red dependency that keeps it red* and re-route to the new
    Thm-5.6 node + the landed `lem:motions-mono-of-graph-le`; flip `\leanok` on statement + proof
    once `rankHypothesis_of_theorem_55_d3` is the genuine `def > 0` feed (the prop's `\lean` pin
    `rigidityMatrix_prop11` is unchanged — the node greens because its `hgen` input now has a
    discharging producer, the green-modulo-→-green transition).
  - **NEW node `thm:theorem-55-6-d3`** (suggest `\label{thm:theorem-55-6-d3}`, panel-layer.tex after
    `thm:theorem-55-d3-instance`): "KT Theorem 5.6 at `d = 3` — every multigraph `G` is realizable at
    rank `D(|V|−1) − def(G̃)`," `\lean{…rankHypothesis_of_theorem_55_d3}` `\leanok`,
    `\uses{thm:theorem-55-d3-instance, lem:motions-mono-of-graph-le, lem:subgraph-minimality,
    prop:rigidity-matrix-prop11}` (+ the strip brick if it earns a node — likely NOT, it is
    `\uses`-only infra per the include/skip bar). Prose: KT p. 670, the strip + projective-move-free
    re-add; one honest sentence that the homogeneous re-add is free (`exists_extensor_in_two_panels`)
    where KT invokes projective invariance.
  - **`thm:theorem-55`** stays red (general-`d`, Phase 23) — untouched.

  **Statement-grep gate (per-slice):** L10b changes `theorem_55_all_k`'s exposed shape (or adds a
  sibling) — grep `blueprint/src` for `theorem_55_all_k` before committing the slice
  (`CLAUDE.md` *Structural-edit phases*).

**(e) Build order + estimate.** L10a → L10b (settle the (c) FLAG FIRST) → L10c → L10d. **If both
flags resolve favorably (the matroid step composes, the all-`k` wrapper is free): ≈ 3–4 commits.**
**If the (c) FLAG is a real gap (a producer assumes `k=0`): L10b grows and the estimate changes** —
that is the phase-close-estimate risk, recorded honestly. The two things L10b's design micro-pass
must confirm before the L10c build: (1) the all-`k` minimal-graph spine is re-exposable at general
`k`; (2) the L10a matroid step (no-deletable-edge ⟺ `IsMinimalKDof`) composes from the landed
`matroidMG`/`isBase` API. Neither is a motive/IH/`def`-reshape; both are buildable-shaped, but both
carry residual P-uncertainty the build resolves — **flagged, not forced.**
