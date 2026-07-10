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

### 1.54 The Leaf-5 feed-audit — `hbase`/`hbaseGP` corrected (not the Pinning.lean base layer); the bare motive found VACUOUS (satisfiable by any connected graph, USER SIGN-OFF flagged); the Lemma-6.5 arm found genuinely missing from `hcontractGP` (2026-06-11)

**(a)/(a1) `hbase`/`hbaseGP`.** Pinning.lean's `theorem_55_base` is framework-level only (`F :
BodyHingeFramework`, two named edges, an LI-extensor hypothesis) — no graph-level form exists.
`hbaseGP` is VACUOUSLY dischargeable: a simple `|V|=2` minimal-0-dof graph does not exist (KT
p. 671's trichotomy — only the parallel-pair case is 0-dof), via
`two_le_crossingEdges_of_isKDof_zero` + `loopless_of_isMinimalKDof` + `hSimple.eq_of_isLink` (one
new lemma, `not_simple_of_isMinimalKDof_of_ncard_two`). `hbase` is reachable only through a
degenerate-selector realization — see (a2).

**(a2) Headline finding.** `HasFullRankRealization` has no link-recording/nonzero-extensor
condition, so it is satisfiable for EVERY connected graph via the degenerate selector `ends :=
fun _ => (a₀, a₀)` (welds every linked pair; every 0-dof graph is connected). One brick
`hasFullRankRealization_of_isKDof_zero` would discharge `hbase`, `hsplit`, AND bare `hcontract`
outright — the bare conjunct is formally vacuous, and `theorem_55_d3`'s mathematical content
lives entirely in the GP conjunct. **Flagged for USER SIGN-OFF**, not decided here: land the
degenerate brick now (recommended — the `d=3` capstone never consumes the bare conjunct) vs.
strengthen the motive immediately (~10+ commits, re-opens the Lemma-5.3/6.2 builds). **Resolved
by §1.55: strengthen, deferred to the all-`k` successor — the degenerate brick was never built.**

**(a3) `hcontractGP`.** `case_I_realization` supplies only KT's 6.3 arm (needs `hcSimple :
(G.rigidContract H r).Simple`, not derivable — `rigidContract_simple` is conditional; KT routes
the failure to Lemma 6.5). The **Lemma-6.5 vertex-removal arm** is genuinely missing (the
phase-close-estimate changer, ~4–6 commits): (1) Claim 6.6, graph side — a vertex-inclusionwise
*maximal* proper rigid subgraph `G′`, with `G″ := G′ + v + {e,f}` rigid via KT Lemma 4.4
(`def(G̃″) ≤ def(G̃′)`), so maximality forces `G = G″`, `0`-dof with a degree-2 vertex `v` whose
`G − v` is minimal-0-dof and simple; (2) the Π°-placement producer, geometric side — reuse the
IH's already-alg-independent normal at `v` as KT's `Π°` (no extension step needed; the landed
triple-LI bridge supplies both side conditions), all bricks landed but the assembly is new and
needs its own signature pin before building; (3) the dispatch, `by_cases` on simple-contraction
existence. **Resolved by §1.55: route (B)** — carry `h65` as a named hypothesis rather than build
the arm in-phase.

**(b) The Thm 5.5→5.6 push at `d=3`.** Reachable at 22h-close: the `def=0`/simple/spanning
stratum only (`rankHypothesis_deficiency_of_theorem_55_d3`), via the GP conjunct +
`finrank_infinitesimalMotions_of_isInfinitesimallyRigidOn_vertexSet` + an off-edge selector
re-aim (`prop11`'s `hC` quantifies over all `e : β`; the motive only records links). Full Thm
5.6 (`def > 0`) needs the all-`k` restructure — the already-adjudicated GAP-6 successor.

**(c) Blueprint plan.** Mint `thm:theorem-55-d3-instance` (green, `\uses` the GAP-6 red node);
mint the named wrapper `case_III_realization` and pin both `lem:case-II-realization` /
`lem:case-III` to it (de-duplicating the wiring lambda); give the GAP-6 carry its own red node
`lem:case-III-nested-rank-lower`; `thm:theorem-55` stays red pending Phase 23.

**(d) The Leaf-5 cut** (superseded by §1.55's revised L5a′–L5e′): L5a (base/degenerate bricks,
gated on (a2) sign-off) → L5b (rewire `theorem_55_d3`) → L5c (the `hcontractGP` arm, route A/B)
→ L5d (the (b) push) → L5e (blueprint).

### 1.55 The §1.54 adjudications (user, 2026-06-11) — Decision 1: strengthen the bare motive to KT's strength at the all-`k` redesign ("22i"), cutting the degenerate brick; Decision 2: route (B), carry `h65`

**(a) Decision 1.** The project's statements must match KT's strength — `HasFullRankRealization`
gets a genuine-hinge conjunct. NOT in 22h: schedule the strengthening together with the
already-adjudicated all-`k` restructure in one successor sub-phase ("22i"), opening with a
single motive design pass (§1.56) that pins both together. Postmortem + rationale: `DESIGN.md`
*Statement faithfulness to the source*.

**(b) Consequence.** The degenerate brick is cut as throwaway; `hbase`/`hsplit`/`hcontract` stay
carried as named hypotheses on `theorem_55_d3` (zero rework, real discharges in 22i); `hbaseGP`
still discharges via the (a1) vacuity lemma. The 22h-close green-modulo surface is the named
family {`h622`, `h65`, `hbase`, `hsplit`, `hcontract`}, tracked via a carries table seeded in
`notes/Phase22i.md` at the 22h→22i boundary.

**(c) The revised cut.** L5a′ (blueprint honesty repairs, docs-only: re-prose
`def:rank-hypothesis`, mint `lem:case-I-dispatch`) → L5b′ (`not_simple_of_isMinimalKDof_of_ncard_two`
+ `theorem_55_d3` reshaped to the full conditioned pair, drop the `.2` projection; mint
`case_III_realization`) → L5c′ (the `hcontractGP` dispatch, `by_cases` on simple-contraction
existence, route B: the negative branch is the named carry `h65`) → L5d′ (unchanged, the (b)
push) → L5e′ (blueprint close). Phase close ≈ 5 commits, green-modulo the named family.

### 1.56 The 22i motive design pass — carrier split (honest bare motive → free-hinge `BodyHingeFramework`; generic motive keeps `PanelHingeFramework`) + the all-`k` four-case reduction principle (2026-06-11)

**(a) The expressiveness finding forcing the carrier split.** KT's panel-hinge realization gives
each edge a **freely chosen** `(d−2)`-flat hinge in `Π(u) ∩ Π(v)`; `PanelHingeFramework` instead
*derives* the hinge as the meet of the two selected normals, which degenerates when adjacent
panels **coincide** — exactly the freedom KT's Lemma 5.3 (parallel-pair base, `Π(u)=Π(v)` with
two distinct genuine hinges) and Lemma 6.2 (contraction splice, `Π(a)=Π(b)=Π(v*)`) need. Verdict:
the honest bare motive moves to the free-hinge `BodyHingeFramework` carrier plus an explicit
panel assignment; the generic (simple-case) motive keeps `PanelHingeFramework` unchanged (every
two adjacent panels are transversal in general position, nothing lost — the entire 22a–22h GP
spine survives untouched but for the rank form of (c)).

**(b) The pinned motives M1–M5** (checkdecls-gated at L0). **M1** `ExtensorInPanel` — new
containment predicate (pointwise form: spanned by points of the normal's hyperplane); **V1**
(exact formulation) resolved at §1.57. **M2** `HasPanelRealization` — the new honest bare motive:
`BodyHingeFramework` + an explicit panel assignment, genuine hinges (`≠0`) and containment
required on links only, panels nonzero on `V(G)` only, concluding the ℤ-cast rank equality at
`G.deficiency n` (not `≥`; closed via **B2**). **M3** `HasGenericFullRankRealization` restated in
place, same carrier, same ℤ-cast rank-equality conclusion (equivalent to the rigid form at
`def=0` via **B1**). **M4** the conditioned pair `Pc G := (G.Simple → generic) ∧ (bare)`
unchanged in shape; the forgetful map `hasPanelRealization_of_generic` is no longer
projection-trivial (needs the M1 meet-decomposition). **M5** `HasFullRankRealization` deleted,
`HasPanelRealization` its honest replacement; every blueprint node naming the old motive restates
per the structural-edit gate. (Corrected at §1.57: an extensor-coercion fix, M5's deletion
re-timed to L9, an `hD`→`hn` flag.)

**(c) The all-`k` reduction principle** `minimal_kdof_reduction_all_k` (NEW, beside the untouched
0-dof `minimal_kdof_reduction[_full]`): KT's four-case `|V|`-recursion (`hbase`/`hcut`/`hcontract`/
`hsplitPos`/`hsplitZero`) with the IH quantified at every dof, base at `ncard ≤ 2` (KT's Lemma-6.1
cut-sides of size 1 fold into the base rather than being excluded). New predicate **V2**
`G.TwoEdgeConnected` (the crossing-edge count, including connectivity). New combinatorial bricks:
the `|V|≤2` trichotomy, the cut-edge decomposition (KT Lemma 3.6 + 3.3), KT Lemma 4.8 (`k>0`
split, the dof decrements). (Corrected at §1.59: the IH must carry the same `Nonempty` guard as
the base.)

**(d) The case-producer map.** `hbase` — the `|V|=2` trichotomy, with the parallel-pair case the
genuinely new Lemma-5.3 geometric brick (re-aiming `theorem_55_base` as the rank engine; GP
conjunct vacuous via L5b′'s vacuity lemma). `hcut` — NEW KT Lemma 6.1 (cut-edge decomposition +
block-triangular rank addition over the cut row; the project's fixed-seed style makes
transversality automatic, **V5**). `hcontract` — dispatch on `G.Simple`; non-simple is NEW KT
Lemma 6.2 (the N6a splice re-aimed at the honest carrier, **V6**). `hsplitPos` — NEW KT Lemma 6.8
assembly (degree-2 vertex, a NEW Lemma-4.8 dof-decrement, the landed eq.-(6.12) placement, then
the Lemma-5.2 shear transfer, **V7**: how much of the 22h W-suite reuses). `hsplitZero` — the
landed 22h Case-III producer restated with `h622` now *derived* from the all-`k` IH at `G−v`
(**V8**: the subfamily extraction generalized to rank form); its bare conjunct is free.

**(e) The spine.** `theorem_55_generic` → `theorem_55_all_k`; bare `theorem_55` superseded and
deleted, `thm:theorem-55` re-pinned (green at `d=3`, red only for general-`d`). The `h65`
discharge is the unchanged §1.54(a3) plan. Theorem 5.6 at `d=3` (the `def>0`
`prop:rigidity-matrix-prop11` feed): strip to a deficiency-preserving minimal-k-dof spanning
subgraph (NEW greedy-deletion brick), apply the instance, re-add edges (**V9**: the homogeneous
projective move is expected free). Corollary 5.7 stays Phase 26.

**(f) Bridges (L0).** **B1**: at `def=0` the ℤ-cast rank equality ⟺ `IsInfinitesimallyRigidOn`.
**B2**: the universal `V(G)`-relative upper bound given genuine hinges on links (**V10**, the
relative form of the landed hub bound) — lets every producer prove `≥` and conclude the M2/M3
equality.

**(g) Verification items V1–V10** (resolved at each layer's design pass): `ExtensorInPanel`'s
form; the `TwoEdgeConnected` predicate; `exists_degree_le_two` dof-agnosticity;
`rigidContract_isMinimalKDof`'s all-`k` generalization; the Lemma-6.1 transversality route; N6a's
honest-carrier restate; the W-suite reuse at `k>0`; the subfamily extraction at rank form; the
homogeneous projective-move freeness; the relative hub bound B2.

**(h) The layer plan** (each L-layer opens its own signature pin; the carries table + checklist
live in `notes/Phase22i.md`): **L0** motives+bridges → **L1** combinatorial bricks → **L2**
`minimal_kdof_reduction_all_k` → **L3** base producer → **L4** Lemma 6.1 → **L5** Lemma 6.2 + the
6.3/6.5 restate → **L6** Lemma 6.8 → **L7** the Case-III rewire → **L8** the 6.5 arm (§1.54(a3))
→ **L9** the spine + instance + blueprint close → **L10** Thm 5.6 at `d=3`. Estimate ~20–30
commits (tracked in `notes/Phase22i.md`).

### 1.57 The L0 signature pin — V1 resolved (pointwise `ExtensorInPanel` + `k=2` meet-decomposition lemma), V10 resolved (B2 via a relative re-derivation, no `reaim`), M1–M5/B1/B2 pinned, L0a–L0e slice cut (2026-06-11)

**(a)** V1 resolved: **pointwise** wins over the annihilator-dual/meet-image alternatives (the
native output of the Lemma-5.3/6.2 constructions; the alternatives would tie the general-`k`
*definition* to `d=3`-only exterior-power machinery). `ExtensorInPanel` (RigidityMatrix.lean,
graph-free geometry section) fixes two `§1.56`-sketch errors: the coercion (`extensor` lands in
the full `ExteriorAlgebra`, not the graded `ScrewSpace` piece — the equality goes through the
submodule coercion) and placement (RigidityMatrix.lean, not PanelLayer — the def needs only
`extensor`/`ScrewSpace`/`⬝ᵥ`). The meet-decomposition lemma
(`exists_extensor_eq_panelSupportExtensor`) is pinned at `k = 2` only — every consumer is a
`d=3` producer and the engine is the `Fin 4` PanelLayer duality; general-`k` meet is Phase-23
work. Landed L0a (`6d2fb4a`).

**(b)** V10 resolved: **B2 is a `V(G)`-relative re-derivation, not a `reaim`.**
`finrank_partitionCutMap_codomain`'s all-`e` `hC` is an artifact — it only ever consumes `hC`
on crossing edges, which are links by definition, so the relative siblings take the per-link
`hC` directly; no `reaim` re-aim of off-link selectors is needed anywhere in the B2 chain
(`reaim` still feeds `rigidityMatrix_prop11`'s genuinely all-`e` `hC` unchanged). The genuine
gap is the ambient complement count: the deficiency-attaining partition must additionally
separate every `V(G)ᶜ` body into its own part (junk bodies carry no link, so the crossing count
is unchanged while `finrank_partitionConstant`'s **exact** `D·|range f|` form banks the extra
parts as profit). Three bricks close it — the `|range f|`-form motion bound, a
label-normalization + complement-separation refinement, and the relative hub
`screwDim_mul_compl_add_deficiency_le_finrank_infinitesimalMotions` + B2 itself
(`finrank_span_rigidityRows_add_deficiency_le`), both PanelLayer.lean, taking
`hn : bodyBarDim n = screwDim k` rather than hardcoding `n := k+1`. Landed L0b/L0c (`6bcb4eb`,
`b755bc1`); confirmed downstream citer `PanelLayer.lean:2124`.

**(c)** B1 (GenericityDevice.lean) — the `def = 0` bridge,
`isInfinitesimallyRigidOn_vertexSet_iff_finrank_span_rigidityRows`:
`IsInfinitesimallyRigidOn V(G) ↔ finrank(span rigidityRows) = D(|V(G)|−1)` (ℕ-form, no
genuine-hinge hypothesis in either direction — `hC` enters only at B2). Forward is W2 verbatim;
reverse routes through the shared complement brick + N3. Landed L0b (`6bcb4eb`).

**(d)** M2–M5, exact statements/placements. **M2** `HasPanelRealization k n G` (PanelHinge.lean,
root `Molecular` namespace — the Molecular `BodyHingeFramework` has no `ends` field, so the
per-link containment is stated relationally, confirmed against the carrier): existence of a
framework + normal assignment with nonzero per-vertex normals, per-link `ExtensorInPanel`
containment in both endpoints' panels, and the ℤ-cast rank-deficiency equality. **M3**
(`HasGenericFullRankRealization`, in place) gains `n` and restates its rank conjunct on
`Q.toBodyHinge.rigidityRows` (so M4's transfer to M2 is literal). **M4**
`hasPanelRealization_of_generic` (PanelHinge.lean, `k = 2`): the forgetful map from the GP
motive, giving the conditioned pair
`Pc G := (G.Simple → HasGenericFullRankRealization k n G) ∧ HasPanelRealization k n G`. **M5**:
`HasFullRankRealization` **cannot** be deleted at L0 (live GenericityDevice/`theorem_55`
consumers restate at their own layers L3/L5/L9); L0 only takes the weak motive off the live
conditioned spine and drops its `def:rank-hypothesis` pin, deleting only the now-consumer-free
old forgetful `hasFullRankRealization_of_generic` (doc-comment references only). Landed L0d
(`652ea99`).

**(e)** The L0 slice cut, all landed 2026-06-11/12 (Phase 22i): **L0a** `ExtensorInPanel` + the
meet-decomposition lemma (`6d2fb4a`); **L0b** the complement brick + B1 (`6bcb4eb`); **L0c** the
`|range f|` bound + normalization/refinement + relative hub + B2 (`b755bc1`); **L0d** M2 + M4 +
the `def:genuine-hinge-realization` blueprint flip (`652ea99`); **L0e** the in-place restates
(M3's `n` + rank conjunct, the conditioned-pair swap, `theorem_55_d3`'s re-typed carries, the GP
producers' conclusion seams, `def:rank-hypothesis` re-prose) — cut M3-first if oversized, landed
as `db618c9` (M3-first bulk) + `e68cc4a` (the pair-swap). Two flags recorded for L9/L10:
`theorem_55_d3`'s `hD : 6 ≤ bodyBarDim n` tightens to `hn : bodyBarDim n = screwDim 2` at the
L9 restate (the `def = 0` GP producers keep `6 ≤`); `rigidityMatrix_prop11` + the L10 feed keep
the all-`e` `hC` + `reaim` pattern unchanged.

**(f)** Blueprint: `def:genuine-hinge-realization` (panel-layer.tex) restated to the M2 form at
L0d, `\uses def:D-deficiency` added; `def:rank-hypothesis` drops the `HasFullRankRealization`
pin at L0e, gains the B1 bridge; `lem:trivial-motions-rank-bound` (genericity-and-count.tex)
joins the relative hub + B2 at L0c; `thm:theorem-55`/`thm:theorem-55-d3-instance` untouched at
L0 (their restates are L9's) — the d3-instance's `\lean` list survives L0e verbatim under new
statement shapes, the case the structural-edit grep gate exists for.

### 1.58 The L1 signature pin — V2 resolved (`TwoEdgeConnected` = the labeling-free `cutEdges` count over nonempty proper vertex sets, connectivity included), V3 resolved (the landed swap proof is all-`k` after one re-routed contradiction; the `= 2` upgrade takes the V2 predicate as hypothesis), V4 resolved (mechanical in-place), a KT-numbering correction (the landed `splitOff_isMinimalKDof` is KT **4.8(i)**, not 4.7), KT 3.6 by a pure partition argument (no matroid direct sum), the KT-4.8(ii) cluster decomposed (the reverse forest direction KT 4.2 is the one genuinely new engine), and the L1a–L1j slice cut (2026-06-11)

**(a)** KT-numbering corrections (verified against the PDF; §1.56 cited partly from memory).
The landed `splitOff_isMinimalKDof` is **KT 4.8(i)**, not 4.7 (§1.56(c)'s "unlike the landed
4.7" misnames it). Roster: 4.1/4.2 = forest surgery (split + reverse); 4.3 = the splitting-off
dichotomy (two-sided bound landed as `splitOff_deficiency_le`/`_ge`; the base-criterion clause
deliberately deferred in Phase 20, now needed for 4.7/4.8(ii)); 4.4 = `def(G̃ᵥ) ≥ k` landed
(`removeVertex_deficiency_ge`), the equality clause not; 4.5(ii)/4.7/4.8(ii) not landed. KT 3.2
(p. 657): only its `|V|=2` parallel-class-bound consequence is needed, not the full statement.

**(b)** V2 resolved: `TwoEdgeConnected` is the labeling-free cut count, connectivity included.
`cutEdges G V' := {e ∈ E(G) | ∃ x y, IsLink e x y ∧ x ∈ V' ∧ y ∉ V'}` (Deficiency.lean);
`TwoEdgeConnected G := ∀ V', V'.Nonempty → V' ⊂ V(G) → 2 ≤ (cutEdges V').ncard`, plus a transfer
lemma to the landed `cutLabeling`/`crossingEdges` API and the two producers
`twoEdgeConnected_of_isKDof_zero` / `two_le_degree_of_twoEdgeConnected`. Connectivity is
automatic (a component's `cutEdges = ∅ < 2`); at `|V(G)| ≤ 1` the predicate is vacuous (KT's
convention). Landed L1a.

**(c)** V3 resolved: yes, and stronger than expected — the landed swap proof (`no_rigid_edge_
count`) generalizes **in place** to all-`k`, because its fundamental-circuit swap never
structurally uses `def = 0` (the `X ∩ ẽ = ∅` contradiction re-routes uniformly through
`deficiency_nonneg` to force `k = 0`). In-place all-`k` restates, ReducibleVertex.lean:
`no_rigid_edge_count`, `exists_degree_le_two`, `exists_degree_eq_two` (KT 4.6 restate, now
hypothesis `htec : TwoEdgeConnected` in place of the `def = 0`-only crossing-edge call — two
call-site ripples, both ` k = 0`), `simple_of_isMinimalKDof_of_noRigid` (G0, zero ripple).
Landed L1c.

**(d)** V4 resolved: mechanical. `rigidContract_isMinimalKDof`'s matroid side
(`contraction_isMinimalKDof`) was already all-`k`; the graph bridge generalizes in place (its
one `0`-specific proof line becomes `= k`, same `linarith`). Blueprint
`lem:rigidContract-isMinimalKDof` restates all-`k` in the same commit. Landed L1c.

**(e)** The `|V| ≤ 2` trichotomy (KT p. 671 base + the Lemma-3.2 consequence), Deficiency.lean:
`deficiency_of_edgeSet_empty` (no edges ⟹ `def = D(|V|−1)`), `deficiency_of_single_edge`
(`def = 1`), `edgeSet_ncard_le_two_of_isMinimalKDof_of_ncard_two` (the Lemma-3.2 parallel-class
bound: minimality at `|V|=2` caps `|E| ≤ 2`, via a `0`-dof two-edge restriction whose base is
`M(G̃)`-independent), and the packaging `isMinimalKDof_ncard_le_two_trichotomy` (the three-way
disjunction on `|V| ≤ 2`). **The L2 floor flag — this note is the "§1.58(e)(iv)" §1.59's
header cites:** §1.56(c)'s "vertex floor drops to nothing" over-reaches at `V(G) = ∅` (an
empty-carrier `deficiency` is an `iSup` over an empty labeling type — junk, and M2's rank
conjunct is false there) — the L2 principle must instead conclude
`∀ k G, IsMinimalKDof n k → V(G).Nonempty → P G`, with `hbase` covering `1 ≤ ncard ≤ 2`;
sound because Lemma 6.1's cut sides are nonempty by construction. Landed L1b.

**(f)** The cut-edge decomposition (KT Lemma 3.6, p. 659) — a pure partition argument, **no
matroid direct sum** (unlike KT's `M(G̃) = M(G̃₁)⊕M(G̃₂)⊕M(G̃₃)` route): both inequalities fall
to the landed `partitionDef` machinery (optimal side-partitions combine for `≥`; an arbitrary
labeling refines to a side-separated one without decreasing `partitionDef` for `≤`, since
`d_G(P) ≤ 1`). Five bricks + packaging, Deficiency.lean: `partitionDef_congr`,
`partitionDef_comp_of_injOn`, `partitionDef_split_of_sides`,
`exists_sides_separated_partitionDef_le`, `deficiency_eq_of_cutEdges_ncard_le_one` (the Lemma
3.6 statement itself, both `d_G(P) ∈ {0,1}` arms), and the `hcut`-producer opener
`exists_cut_decomposition_of_not_twoEdgeConnected`. Landed L1d/L1e.

**(g)** The KT-4.8(ii) cluster — decomposed; the reverse forest direction (KT 4.2) is the one
genuinely new engine, everything else rides landed machinery. Dependency chain: 4.2(i)/(ii) →
{4.4-equality, 4.3(ii)-reverse}; 4.5(ii) + 4.4-equality → 4.7 all-`k`; 4.3(ii)-forward
(mechanical) + 4.7 + 4.2(ii) + a commuting square → 4.8(ii). New leaves, all ForestSurgery.lean
unless noted: **KT 4.2** `splitOff_indep_extend_of_fiber_lt`/`_subset` (the forest-reindex +
fiber-relabel extension of a split-side independent set back up, with two new reverse-direction
acyclicity bricks — pendant insert + the through-`v` swap); **KT 4.5(ii)**
`indep_edgeSet_mulTilde_of_noRigid_of_pos` (ReducibleVertex.lean; a spanning-rigid-subgraph
contradiction) + its base-uniqueness corollary; **KT 4.4-equality**
`exists_isBase_vb_fiber_eq_one_of_removeVertex_isKDof` (4.2(i) at `h'=0`); **KT 4.7 all-`k`**
`removeVertex_deficiency_gt_of_noRigid` (the `k=0` arm inline from the landed
`splitOff_isMinimalKDof`; the `k>0` arm from 4.4-equality + 4.5(ii)-uniqueness, needing `hD : 3 ≤
D`); **KT 4.3(ii)** forward = the landed `splitOff_exists_base_inter_fiber_lt` restated in place
at general `k`, reverse = NEW `splitOff_isKDof_of_exists_base_inter_fiber_lt` (via 4.2(i));
**the commuting square** `induce_insert_splitOff` (Operations.lean, `Graph.ext`); **KT 4.8(ii)**
`splitOff_isMinimalKDof_of_pos` (the assembly: rule out `def(H) = k` via a proper-rigid-subgraph
contradiction built from 4.3(ii)-forward + the commuting square + 4.2(i); minimality at
`def(H) = k−1` splits on `e = e₀` vs. `e ≠ e₀`, closing via 4.7 resp. 4.2(ii) + the survivor
conjunct). Landed L1f–L1j.

**(h)** Blueprint dispositions (structural-edit mode; each lands with its Lean slice). New
nodes: `def:cut-edges-2ec` ((b)), `lem:two-vertex-trichotomy` ((e)), `lem:cut-edge-decomposition`
((f)), `lem:edge-splitting` (KT 4.2), `lem:edge-set-indep-pos` (4.5(ii)),
`lem:removal-deficiency-strict` (4.7, sibling of `lem:removal-deficiency`),
`lem:splitoff-kdof-criterion` (4.3(ii)), `lem:reduction-step-pos` (4.8(ii)). Restated in place
(statement-grep gate per slice): `lem:no-rigid-edge-count`, `lem:low-degree-vertex`,
`lem:reducible-vertex` (gains the 2EC hypothesis), `lem:simple-minimal-noRigid`,
`lem:rigidContract-isMinimalKDof`.

**(i)** The L1 slice cut, build order **L1a → {L1b, L1c, L1d, L1f, L1g} (independent) → L1e,
L1h → L1i → L1j** (~10 commits; all landed 2026-06-11/12, Phase 22i): **L1a** V2 — `cutEdges` +
`TwoEdgeConnected` + bridges + `def:cut-edges-2ec` (`fec8775`). **L1b** the `|V|≤2` trichotomy
(`4af8b7d`). **L1c** the in-place all-`k` restates V3/V4/G0 (`b5337b2`). **L1d** KT 3.6 part 1,
the three `partitionDef` bricks (`8fde55b`). **L1e** KT 3.6 part 2, the refinement bound + the
`hcut` packaging (needs L1a+L1d). **L1f** KT 4.5(ii) + uniqueness (`3856f47`). **L1g** the
reverse acyclicity bricks (`9019d5e`, escalation retry after a sonnet BLOCK). **L1h** KT
4.2(i)/(ii) (needs L1g). **L1i** 4.4-equality + 4.7 + 4.3(ii) (needs L1f+L1h). **L1j** the
commuting square + 4.8(ii) (`07cfa24`, needs L1h+L1i). L1's outputs feed L2 (the V2 predicate +
the (e) floor flag), L3 (the trichotomy), L4 (the cut decomposition), and L6 (the 4.6-restate +
4.8(ii)).

### 1.59 The L2 signature pin — `minimal_kdof_reduction_all_k` pinned with the §1.58(e)(iv) floor flag implemented (conclude at `V(G).Nonempty`, `hbase` covers `1 ≤ ncard ≤ 2`, **and the IH carries the same `Nonempty` guard** — the one statement-level delta the flag forces beyond its own wording); the five-slot-vs-landed-inventory audit clean; the principle needs no `hD`/`hfresh`/`[Finite β]` (the `_full` precedent); the legacy `minimal_kdof_reduction[_full]` stays beside it, neither derivable from the other; blueprint: NEW node `thm:minimal-kdof-reduction-all-k` (2026-06-12)

**(a)** `minimal_kdof_reduction_all_k` (ForestSurgery.lean, beside `minimal_kdof_reduction_full`)
pins KT's four-case `|V(G)| ≥ 3` split (p. 671, verbatim: ¬2EC / proper rigid subgraph / 2EC +
no-rigid `k>0` / 2EC + no-rigid `k=0`) plus a `hbase` slot, concluding
`∀ k G, IsMinimalKDof n k → V(G).Nonempty → P G`. Design notes: **(i)** the §1.58(e)(iv) floor
flag forces the IH itself to carry the same `Nonempty` guard (weaker than the legacy `2 ≤
ncard`; every IH target is nonempty by construction) — §1.56(c)'s unguarded draft IH was
unprovable, this is the flag doing its job. **(ii)** the split is KT p. 671 verbatim, re-checked
against the PDF; `hcontract` carries no 2EC hypothesis, paper-faithful. **(iii)** no `hD`/
`hfresh`/`[Finite β]` — the `_full` precedent, all reduction left to the producers; the only
non-classical content is the `0 ≤ k` dispatch from `deficiency_nonneg`. **(iv)** `hsplitZero`
is pinned at instantiated `IsMinimalKDof n 0`, matching the legacy `_full` `hsplit` shape.
**(v)** proof = `Nat.strong_induction_on` on `V(G).ncard` generalizing `k G` (the `_full`
skeleton + `k`), three nested classical `by_cases` at `3 ≤ ncard`.

**(b)** The five-slot-vs-landed-inventory audit is clean: `hbase` ↔
`isMinimalKDof_ncard_le_two_trichotomy` (L3); `hcut` ↔
`exists_cut_decomposition_of_not_twoEdgeConnected` (L4); `hcontract` ↔
`rigidContract_isMinimalKDof`, all-`k` (L5); `hsplitPos` ↔ `exists_degree_eq_two` +
`splitOff_isMinimalKDof_of_pos` (L6); `hsplitZero` ↔ the landed 22h Case-III chain restated,
a strict superset of the legacy `_full` `hsplit` slot (gains `htec` + the all-`k` IH, the
entire point of the `h622` derivation at the `k'`-dof `G_v`) (L7+L9). Every slot's hypothesis
set matches its discharging producer exactly, modulo producer-only extras (`hD`, `hfresh`).

**(c)** `minimal_kdof_reduction[_full]` (KT Theorem 4.9, `k = 0` only) stays **side by side**
with the new principle — neither derives the other (the legacy's `hbase` is `ncard = 2` only
and its motive is `0`-dof-specific; the new principle's case lattice has no ¬2EC arm at `k=0`,
vacuous by `twoEdgeConnected_of_isKDof_zero`). The legacy keeps its `thm:minimal-kdof-reduction`
pin and its consumers until L9 re-pins the spine onto the all-`k` principle. (This is the
"two-principle co-existence rationale" `Reduction.lean:734` points at.)

**(d)** Blueprint: NEW node `thm:minimal-kdof-reduction-all-k` (molecular-induction.tex,
directly after `thm:minimal-kdof-reduction`), `\lean{Graph.minimal_kdof_reduction_all_k}` +
`\leanok` landing with L2, `\uses{def:k-dof, def:cut-edges-2ec, def:rigid-subgraph}` only (no
internal reduction, so no `lem:reduction-step*`). Prose: not a numbered KT theorem — the
induction skeleton underlying KT Theorem 5.5's proof (§6 opening + IH (6.1)).

**(e)** The L2 slice: one commit (the decl + the green blueprint node), additive, no
statement-grep ripple. Landed.

### 1.60 The L3 signature pin — the base producer (`hbase` carry): the genuine-hinge `|V| ≤ 2` base built on the landed trichotomy, the parallel-pair `k = 0` arm as the one new geometric brick (two non-proportional extensors inside a common panel `n^⊥`, fed to `theorem_55_base`), the rank conjunct closed by B1, re-aimed into `Pinning.lean`'s `theorem_55_base` as the rank engine; `theorem_55_base` is the *right* home but only as the LI-extensor-pair *engine* — the graph-level producer is NEW (2026-06-12)

**The corrected target shape.** §1.56(c)/(d)'s "re-aim `theorem_55_base`" carries-table entry
needed two fixes against the *landed* L2 principle (§1.59) and `theorem_55_base` itself: the
slot is **all-`k`, `Nonempty`, `ncard ≤ 2`** — not `ncard = 2`, not 0-dof-only — so the producer
must also cover `ncard = 1` (`E = ∅`), a real extra arm, not bookkeeping; and `theorem_55_base`
is the right home only as the **framework-level LI-extensor-pair rank engine**, not the
graph-level base producer itself — that producer (dispatching the trichotomy, constructing the
parallel-pair framework, lifting via B1) is new Lean sitting beside it.

**(a)** The pinned producer `theorem_55_base_producer` (Pinning.lean; `hD : 6 ≤ bodyBarDim n`,
`G.IsMinimalKDof n k`, `V(G).Nonempty`, `V(G).ncard ≤ 2`) concludes the strong conditioned pair
`(G.Simple → HasGenericFullRankRealization 2 n G) ∧ HasPanelRealization 2 n G` — the L9-spine
`Pc` motive (§1.56(b) M4) — rather than the legacy `HasPanelRealization`-only `hbase` slot; for
the *current* legacy-spine `theorem_55_d3` it also discharges the present `hbase` slot via the
`.2` projection, in the same commit.

**(b)** Trichotomy dispatch (`isMinimalKDof_ncard_le_two_trichotomy`), three arms: **(i)**
`E(G) = ∅` (`ncard ∈ {1,2}`), target rank `0`, vacuous per-link conjunct. **(ii)** single edge
(`ncard = 2`, `k = 1`), target rank `D − 1`, one genuine hinge via the single-row rank fact.
**(iii) THE NEW GEOMETRIC BRICK — the parallel pair (`ncard = 2`, `k = 0`, KT Lemma 5.3 p. 670),**
target rank `D` (full) — two non-proportional extensors `C_e, C_f` in a common panel `n^⊥`, fed
to `theorem_55_base`, lifted to `finrank(span rigidityRows) = D` via B1. The GP conjunct does
real work only in arm (ii) (a `def = 1` generic construction at rank `D − 1`); it is vacuous in
(i) (empty) and excluded in (iii) (parallel pairs are non-simple).

**(c)** The new construction: two non-proportional `ScrewSpace 2` extensors inside a common
hyperplane `n^⊥ ⊆ ℝ⁴` (`exists_linearIndependent_extensor_pair_perp`), built from three LI
vectors spanning the 3-dim `n^⊥` and the wedge-LI fact `LI ![a,b,c] → LI ![a∧b, a∧c]`
(a Grassmann basis fact, not mathlib-native at the time of this pin).

**(d)** The rank conjunct closes uniformly by the pattern **producer supplies `≥`, B2 supplies
the universal `≤`**: arm (iii) closes by B1 (an equality at `def = 0`: rigid ⟺ full rank); arm
(ii) is not rigid, so the lower bound is the single-row block's `≥ D − 1` and B2
(`finrank_span_rigidityRows_add_deficiency_le`) gives `≤ D − 1`, antisymmetry closing the rest;
arm (i) is `0 = 0`. This is the base-case instance of the closing pattern every later
reduction-case producer (L4 onward) reuses.

**(e)** GP conjunct under `G.Simple`: arm (iii) excluded
(`not_simple_of_isMinimalKDof_of_ncard_two`, the landed `theorem_55_d3` `hbaseGP` witness); arm
(ii) is the one base arm with genuine GP content (a `def = 1` generic realization via the
single-row count); arm (i) is vacuous (rank 0).

**(f)** Blueprint: new node `lem:theorem-55-base-producer` in panel-layer.tex (after
`lem:theorem-55-base`), `\uses` the trichotomy, `theorem_55_base`, the parallel-hinges-full leg,
and the two motives. Additive — the carry-discharge prose on `thm:theorem-55-d3-instance`
updates only at L9 (when the spine swaps to the all-`k` principle), not here.

**(g)** L3 slice cut, construction first: **L3a** `exists_linearIndependent_extensor_pair_perp`
(+ the wedge-LI helper); **L3b** `theorem_55_base_producer` (dispatch + arms + GP pair) + the
legacy `hbase` rewire. **V-base (L3, §1.60(g)): RESOLVED.** The wedge-LI fact, the single-hinge-row
rank lemma, and the single-edge GP infra are all bounded, non-research-shaped.

### 1.61 The L4 signature pin — Lemma 6.1, the cut-edge / not-2-edge-connected case (`hcut`): one graph-level producer concluding the conditioned pair `Pc`, consuming the L1e cut decomposition + the smaller-graph IH; V5 RESOLVED — the closing `≤` is free (B2, landed), the substance is the lower bound `≥`, established by a NEW vertex-disjoint block-rank-addition lemma (the project's fixed-seed route replaces KT's isometry); the disconnected/connected split of KT collapses into one `cutEdges.ncard ∈ {0,1}` arithmetic; sliced L4a (the block-rank-addition brick, bare conjunct) → L4b (the producer + GP conjunct) (2026-06-13)

**Citation.** Katoh–Tanigawa 2011, *Discrete Comput. Geom.* **45**, 647–700; **Lemma 6.1**, §6.1,
p. 672 (the not-2EC case of the all-`k` Theorem 5.5 induction). The cut decomposition
`k = k₁ + k₂ + 1` is KT's **Lemma 3.6** (p. 658) + **Lemma 3.3** (sides minimal, p. 657); the
cut-row rank `D − 1` and the pin-a-body equality are **Lemma 5.1** (p. 668, the Tay–Whiteley fact).

**(a)** V5 RESOLVED: the closing `≤` is already free — **B2** (`finrank_span_rigidityRows_add_
deficiency_le`, landed, `V(G)`-relative) gives the upper bound for *any* body-hinge with genuine
hinges, so the entire L4 difficulty is the **lower bound** `≥ D(|V|−1) − k`; antisymmetry with
`def(G̃) = k` closes it. This is the same `≥`-then-B2 closing pattern §1.60(d) pinned for the
base producer's single-edge arm — B2 is the universal `≤`, the producer only ever supplies `≥`.
B1 does NOT apply (`def(G̃) ≥ 1` generally, so the combined framework is not rigid). The project
builds the combined `BodyHingeFramework` directly on the shared `α` (edge-label dispatch: `F₁`'s
extensor on `E₁`, `F₂`'s on `E₂`, a genuine cut extensor `C_cut` on the cut edge) rather than
KT's isometry-transversality route; for the **bare** conjunct transversality is not even needed
(any flat in a common panel has `C_cut ≠ 0`) — it is a GP-conjunct-only concern.

**(b)** The lower bound — the block-rank-addition brick
(`BodyHingeFramework.le_finrank_span_rigidityRows_of_cut`, `lem:rigidityRows-cut-rank-add`): for
a cut with ≤ 1 crossing edge, `finrank(span R₁) + (D−1)|cut| + finrank(span R₂) ≤
finrank(span F.rigidityRows)`, via disjoint coordinate-block independence (each side's rows are
functionals reading only its own bodies) — the multi-group analogue of the landed single-edge
split `span_rigidityRows_eq_sup_span_panelRow_edge`. Combined with the IH ranks and the L1e
arithmetic `k = k₁+k₂+D−(D−1)|cut|`, this gives exactly the target `D(|V|−1) − k`. *Buildable*,
KT's elementary block-triangular argument; Flag V5-a (coordinate-restriction injection vs. the
motion-side dual route) resolved at the build. Cut-edge arm (`lem:case-cut-edge-realization`) —
V5-a resolved, canonical.

**(c)** The bare conjunct `HasPanelRealization 2 n G` (**L4a**): assemble `F`/`normal` from the
two IH side frameworks + a genuine cut extensor; rank `≥` from (b) + IH + arithmetic, `≤` from
B2, antisymmetry. Transversality-free, seed-free — *buildable from L4a + the IH + B2* alone.

**(d)** The GP conjunct `G.Simple → HasGenericFullRankRealization 2 n G` (**L4b**, where
transversality genuinely bites): each side's IH GP realization is at its *own* independent
alg-indep seed; combining into one GP framework on `G` needs either (Route GP-1) a shared
re-seeded IH — likely a statement-level IH change — or (Route GP-2) proving the two seeds'
union alg-independent, a standard disjoint-variable-sets `MvPolynomial` fact, recommended but
with the alg-indep-of-disjoint-union lemma and the GP-forces-transversal step left unverified.
**V5-b, the L4b open item** (resolved at §1.62).

**(e)** Blueprint: `lem:case-cut-edge-realization` (molecular-induction.tex),
`\uses{lem:cut-edge-decomposition, def:genuine-hinge-realization, def:rank-hypothesis,
lem:rigidity-matrix-prop11-hub}` + the block-rank brick node if it earns one; additive, no
statement-grep ripple. Greens at the bare conjunct once L4a lands; the GP conjunct greens the
node fully once L4b lands.

**(f)** L4 slice cut: **L4a** the block-rank brick + bare-conjunct producer (*buildable*, first
concrete L4 commit); **L4b** the GP conjunct, gated on the V5-b verdict (Route GP-1 vs GP-2).

*Verification items:* V5-a (buildable, resolved at L4a); V5-b (the genuine open item, resolved
at L4b/§1.62).

### 1.62 The L4b design micro-pass — V5-b RESOLVED: Route GP-2 is viable with NO IH statement-level change; the §1.61(d) "combine the two side seeds" framing rests on a false premise (both halves of it), and the project's actual GP route is the standing **fresh-shared-seed + rational-rank-polynomial non-root** idiom, generalized rigid→deficient by the already-landed W6e rank-input subfamily extractor; the one new project-internal piece is a deficiency-aware rank-polynomial extractor (a near-mechanical copy of `exists_rankPolynomial_of_rigidOn_linking`), no new `MvPolynomial` lemma (2026-06-13)

**Citation.** Katoh–Tanigawa 2011, *Discrete Comput. Geom.* **45**, 647–700; **Lemma 6.1**,
§6.1, p. 672, and the §6 IH (6.1), p. 671. The transcendence-seed device (algebraically-
independent-over-`ℚ` coordinates as the standing inductive genericity choice) is KT's
**footnote 6**, p. 685 — the project's realization of "the choices of `p₁` and `p₂` are
independent."

**(a)** The §1.61(d) framing was wrong on both halves. The project never combines IH seeds: the
landed Case-I GP composer `hasGenericFullRankRealization_of_couple_ofNormals` extracts each
leg's rational rank polynomial, builds *one fresh* combined seed via
`exists_injective_algebraicIndependent_real`, and realizes there — nothing to reseed, no union
to form. And the naive "disjoint variable sets → union alg-independent" fact is false in
general (`AlgebraicIndependent.sumElim_iff` needs the second family alg-indep over the field
*extended by the first*, not an unconditional disjointness fact) — so §1.61(d)'s "recommended"
seed-union route would have been unsound as stated.

**(b)** The genuine V5-b question, restated: not seed-combination, but **rank-lower-bound
transfer across seeds for the deficient (non-rigid) sides.** The existing transfer machinery
(`exists_rankPolynomial_of_rigidOn_linking`) needs rigidity (`def = 0`); the cut sides are
generally `def = kᵢ > 0`, so it does not apply.

**(c)** Resolution — **Route GP-2, viable, no IH change.** Already-landed infra suffices,
because rigidity was only ever used to get a *full-size* independent subfamily. The
rigidity-FREE **W6e** extractor (`exists_independent_panelRow_subfamily_of_le_finrank`, needs
only a rank lower bound `N`) plus the rigidity-free seed-transfer engine
(`exists_polynomial_ne_zero_of_linearIndependent_at_coeffs_subset_range`) give, per side, a
rational polynomial whose non-vanishing forces `rank ≥ Nᵢ := D(|Vᵢ|−1) − kᵢ` at any seed. One
fresh combined seed `q₀` (a non-root of both sides' transfer polynomials + the GP factor) then
puts both sides at their target rank simultaneously, and cross-side transversality follows for
free from global general position at `q₀` (`supportExtensor_ne_zero_of_isGeneralPosition` +
looplessness) rather than KT's isometry. The one new declaration:
**`PanelHingeFramework.exists_rankPolynomial_of_le_finrank_linking`** (GenericityDevice.lean) —
the deficiency-aware sibling of `exists_rankPolynomial_of_rigidOn_linking`, a two-swap copy (the
W6e rank-input extractor in place of the rigid one; the conclusion re-phrased as "rank ≥ N").
*Buildable*, no new `MvPolynomial` lemma. This is **the idiom later sections cite as "the §1.62
deficiency-aware rank-polynomial transfer"** (route 2 of §1.62).

**(d)** The GP-conjunct producer (`case_cut_edge_realization_gp`, CaseI.lean): composes the
landed bare `case_cut_edge_realization` (`.2`) with the new `gp` producer (`.1`, fed the full
conditioned IH) — cut decomposition, side GP realizations from the IH, per-side W6e + the (c)
rank-polynomial extractor, one fresh `q₀` non-root of both sides' polynomials + the GP factor,
the seed-free L4a brick for the combined bound, B2 for `≤`. *Buildable* once (c) lands.

**(e)** Blueprint disposition (settles §1.61(e)): **green-bare + restate-to-`Pc`** —
`lem:case-cut-edge-realization` stays green at the bare conjunct; L4b mints **one new sibling
node** `lem:case-cut-edge-realization-gp` for the GP conjunct, `\uses`-ing the bare node, the
block-rank brick, `def:rank-hypothesis`, prop11's hub, the GP-device chain, and a small node for
the (c) extractor. Splitting (not restating one node) keeps the green-honesty gate honest,
mirroring how `theorem_55_generic` keeps `hsplit`/`hsplitGP` (bare/GP) as *separate* slots. No
statement-grep ripple (both nodes additive).

**(f)** L4b slice cut: **L4b-1** the (c) extractor (first concrete commit, *buildable*);
**L4b-2** the GP producer (d), composing L4b-1 + the IH + the fresh-seed device + the L4a brick
+ B2.

*Verification items:* **V5-b RESOLVED** — a rank-transfer question, not seed-combination; Route
GP-2 viable, no IH change, no new `MvPolynomial` lemma.

### 1.63 The L5 signature pin — Lemma 6.2, the non-simple Case-I branch (`hcontract`): the `hcontract` slot is a `by_cases` dispatch on `G.Simple` (the §1.55(c) precedent generalized to all-`k`), simple → forgetful M4 ∘ the all-`k`-restated GP `case_I_realization` (6.5 sub-arm carried as `h65`, L8), non-simple → the NEW KT Lemma 6.2 coincident-panel splice; V6 RESOLVED — the landed N6a `hasFullRankRealization_of_splice_of_supportExtensor` cannot be re-aimed (it concludes the *deleted* `HasFullRankRealization` and is `PanelHingeFramework`/`ofNormals`-bound), so L5's non-simple branch is a fresh `BodyHingeFramework`-native bare producer mirroring the landed L4a `case_cut_edge_realization` shape, with the coincident-panel cut hinge supplied by the already-landed `exists_extensor_in_two_panels` (which works AT `n=n`); sliced L5a (the non-simple bare producer) → L5b (the simple-branch all-`k` GP restate + the dispatch) (2026-06-13)

> ⚠️ **(c)/(f) SUPERSEDED by §1.64 (2026-06-13).** The splice-brick statement and slice in (c)/(f)
> below are **WRONG** — read §1.64 for the corrected pin; kept here only because (a)/(b)/(d)/(e)
> still stand and §1.64 cites them. The error: the contraction leg was stated as
> `induce ((V(G)∖V(H))∪{r})`, a bare transversality-free split, but `rigidContract` *collapses*
> `V(H)→r` and **keeps** the relabelled crossing edges `induce` drops — a strictly weaker bound the
> producer can't close, and the IH realizes the *contraction*, not the induce-leg. (The bare
> `induce`-brick was built — sonnet primary 90e8d4a — and reverted.)

**Citation.** Katoh–Tanigawa 2011, *Discrete Comput. Geom.* **45**, 647–700; **Lemma 6.2**, §6.2,
p. 673–674 (the non-simple sub-case of the all-`k` Theorem 5.5 induction). The parallel-pair
`G[{e,f}]` proper-rigidity uses the `D`-spanning-tree criterion (§3); the coincident-panel base
realization is **Lemma 5.3** (p. 670); the deleted-`v*`-columns rank invariance is **Lemma 5.1**
(p. 668, Tay–Whiteley); the contraction's smaller-vertex-set minimality is **Lemma 3.5** (p. 658).

**(a) The two-way dispatch — `by_cases G.Simple`.** KT's Lemma 6.2/6.3/6.5 trifurcation on the
proper-rigid-subgraph case collapses to one top-level dispatch (§1.56(d)'s plan): **simple
branch** → forgetful M4 ∘ the all-`k`-restated GP `case_I_realization_all_k` (itself dispatching
6.3-vs-6.5 on `(G.rigidContract H r).Simple`; the 6.5 sub-arm stays carried as `h65` → L8,
untouched by L5); **non-simple branch** → KT Lemma 6.2 (NEW math, L5a), concluding the bare
`HasPanelRealization` conjunct only (the GP `.1` conjunct is vacuous — `¬G.Simple` kills its
antecedent). Fills L2's `hcontract` slot (§1.56(c)), mirroring L4's `hcut`-slot architecture
(separate `.1`-GP / `.2`-bare producers).

**(b) V6 RESOLVED — N6a is dead, not re-aimable.** N6a (`hasFullRankRealization_of_splice_of_
supportExtensor` family, GenericityDevice.lean:915/1095) concludes the deleted `PanelHingeFramework.
HasFullRankRealization` motive and is bound to the derived-hinge `ofNormals` carrier — both wrong
for M2's free-hinge, deficiency-aware conclusion (a coincident-panel hinge needs a genuine
`(d−2)`-flat *inside* the shared panel, which `ofNormals` cannot carry). The honest precedent is
the landed L4a `case_cut_edge_realization` (`BodyHingeFramework`-native, cut hinge via
`exists_extensor_in_two_panels`); L5a builds Lemma 6.2 fresh in that idiom, reusing
`exists_extensor_in_two_panels` at `n₁ = n₂` for the coincident-panel hinge.

**(c) [SUPERSEDED — see §1.64].** Originally pinned the non-simple producer's block-rank brick on
a *bare, transversality-free* `induce`-leg split mirroring L4a's disjoint-block brick. **WRONG**
(see the warning box above) — kept only as the historical (reverted) reference; §1.64 replaces
both the brick and the producer.

**(d) The L5b simple-branch all-`k` GP restate — unaffected by the §1.64 correction.** Restates
`case_I_realization` (CaseI.lean:2155, the `0`-dof-only Lemma-6.3 arm) to all-`k`: `{k : ℤ}`,
`hG : G.IsMinimalKDof n k`, the all-`k` conditioned IH, still carrying `hcSimple` (the Lemma-6.3
hypothesis) as `case_I_realization_all_k`, concluding `HasGenericFullRankRealization`. Flag
**V6-b**: the landed rank-transport leg `rigidContract_exterior_rank_transport_htransport` is
`def = 0`-gated — confirm at build whether it generalizes mechanically. (**Later found NOT
mechanical** — see the §1.64(f) L5b caveat.)

**(e) Blueprint disposition.** L5a mints `lem:case-I-realization-nonsimple` (case-i.tex) for the
non-simple bare conjunct, `\uses`-ing M2, the proper-rigid-subgraph bricks, B2; the (c) block-rank
brick, if it earns its own node, mints `lem:rigidityRows-splice-rank-add` (rigidity-matrix.tex).
L5b restates `lem:case-I-realization` in place to the all-`k` form — **statement change, grep
`blueprint/src` for `case_I_realization`** per the structural-edit gate; `lem:case-I-dispatch`
(the `h65` node) is untouched.

**(f) [SUPERSEDED — see §1.64(f)].** The original L5 slice cut (L5a construction-first, L5b
restate+dispatch) is replaced by §1.64(f)'s three-leaf re-cut (L5a-i/L5a-ii/L5b) once the (c)
brick was found wrong.

*Verification items:* V6 RESOLVED (N6a dead infrastructure); **V6-a** and **V6-b** carried forward
and re-scoped by §1.64.

---

### 1.64 The L5a RE-PIN — correcting §1.63(c)/(f): the contraction leg is `rigidContract` (a COLLAPSE), not `induce`; the (6.3)–(6.5) additivity is a NEW general-rank block-triangular brick assembled from landed rigidity-FREE pieces (`extProj` row-vanishing ⊕ the collapse row-correspondence ⊕ the deficiency-aware `_of_le_finrank` extractor ⊕ the general-rank Lemma 5.1 column-deletion `finrank_pinnedMotions_add_screwDim`); it is **buildable, NO IH/motive change** — but the projected-image-rank step is genuinely new linear algebra (not a one-line brick, not the rigidity-gated `injOn_extProj` route), flagged for the L5a build (2026-06-13)

**Citation.** Katoh–Tanigawa 2011, *Discrete Comput. Geom.* **45**, 647–700; **Lemma 6.2**, §6.2,
p. 673–674. The deleted-`v*`-columns rank invariance is **Lemma 5.1** (p. 668, White–Whiteley),
landed at general rank as `finrank_pinnedMotions_add_screwDim` (RigidityMatrix.lean:2694, NO
rigidity hypothesis, holds at any deficiency). The block-triangular `≥` is KT eq. (6.3), elementary
(`[[A,0],[∗,B]]` has `rank ≥ rank A + rank B`).

**(a) What §1.63 got wrong (verified diagnosis).** Two independent errors: **(1)** the contraction
leg is a *collapse* `rigidContract G H r = (G ＼ E(H)).map (collapseTo r V(H))`
(ReducibleVertex.lean:1052), not `induce` — same vertex set, but it *keeps* the relabelled crossing
edges `induce` drops, so the induce-leg bound is strictly too weak, and the IH realizes the
*contraction*, not the induce-leg (already all-`k` via `rigidContract_isMinimalKDof`, V4).
**(2)** the (6.3)–(6.5) additivity is not a bare span split — L4a's disjoint-block brick needs
vertex-disjoint legs (`S₁⊓S₂=⊥`), but the splice's legs *share* the contracted body `r` with many
crossing edges: a genuine lower-triangular block matrix, not block-diagonal.

**(b) THE KEY SUBTLETY — `def = k > 0` and Lemma 5.1.** The landed `case_I_realization` route is
`0`-dof-bound at the deepest level (its contraction leg is itself minimal-`0`-dof, so
`injOn_extProj_dualMap_rigidityRows`'s full-rigidity gate `Z⊔W=⊤` applies) — unusable once the
contraction is minimal-`k`-dof, `k>0`. KT's actual `k>0` argument uses **Lemma 5.1** (general-rank,
no rigidity: deleting one body's `D` columns preserves rank), not Claim 6.4 (full-rigidity-gated).
Corrected `≥` chain: **(i)** `(extProj V(H)).dualMap` kills the rigid `H`-block rows
(`hingeRow_comp_extProj_eq_zero`, rigidity-free); **(ii)** the surviving rows correspond row-for-row
to the projected contraction rows (`panelRow_collapseTo_comp_extProj_dualMap`, rigidity-free);
**(iii)** that projection deletes exactly the single shared column `r`
(`rigidContract_vertexSet_inter_eq_singleton`), so by Lemma 5.1 it preserves the contraction's rank
`D(|sc|−1)−k`; **(iv)** rank-nullity gives `finrank(span F.rigidityRows) ≥ D + (D(|V|−2)−k) =
D(|V|−1)−k`; B2 (landed, free `≤`) closes by antisymmetry. No motive/IH change, no new
`MvPolynomial` content (the splice is transversality-free — GP fails on coincident panels, exactly
as §1.63(a) had it).

**(c) HONESTY FLAG — the one genuinely-new brick.** Step (b)(iii)'s rank identity at general
(deficient) rank has **no landed precedent** — the landed `injOn_extProj_dualMap_rigidityRows` is
the rigidity-gated (full-injectivity) analogue, not this rank-identity-via-Lemma-5.1 form. All the
constituent pieces are landed and rigidity-free; the math is KT's elementary block-triangular
argument — so this is **buildable, not research-shaped**. But it is a *real new brick* (the
general-rank shared-body block-triangular rank addition over a collapse), likely several commits —
**its own slice (L5a-i)**, not a one-line `\uses` fold as §1.63 assumed.

**(d) The corrected L5a signature(s).** Brick `BodyHingeFramework.le_finrank_span_rigidityRows_of_
splice` (RigidityMatrix.lean, beside L4a's `le_finrank_span_rigidityRows_of_cut`): for `F` on `G`,
proper rigid `H ≤ F.graph` with representative `r`, `screwDim k * (V(H).ncard - 1) +
finrank(span «contraction-realization».rigidityRows) ≤ finrank(span F.rigidityRows)` — the exact
form of the "surviving-rows ↔ contraction correspondence" hypothesis left as a design slot (feed
the IH framework directly vs. reconstruct internally: **V6-a**, resolves at the L5a-i build).
Producer `case_I_realization_nonsimple` (CaseI.lean): same conclusion as §1.63(c)'s but hypotheses
now just `hnsimple : ¬ G.Simple` (the parallel pair `{e,f}` and representative `r := a` are found
internally, not supplied), assembled from the brick + the two IH legs + B2 + the coincident-panel
Lemma-5.3 hinge at `n₁=n₂`.

**(e) Blueprint disposition (unchanged in kind from §1.63(e), corrected in detail).** L5a mints
`lem:case-I-realization-nonsimple` (case-i.tex) **plus** `lem:rigidityRows-splice-rank-add`
(rigidity-matrix.tex, beside L4a's sibling) — the brick now earns its **own** node (not an optional
`\uses`-fold, per (c)), `\uses`-ing Lemma 5.1's node + the `extProj`/Claim-6.4 row-vanishing nodes.
No statement-grep ripple (additive). L5b unchanged from §1.63(d): restates `lem:case-I-realization`
to all-`k` — grep `blueprint/src` for `case_I_realization` per the structural-edit gate.

**(f) The re-cut L5a slice, three leaves (the brick is its own slice, per (c)).** **L5a-i** — the
(d) block-rank brick alone, first concrete commit; **V6-a** (the correspondence-hypothesis form)
resolves here. **L5a-ii** — `case_I_realization_nonsimple` (the (d) producer), beside
`case_cut_edge_realization`. **L5b** — `case_I_realization_all_k` (§1.63(d), unchanged) + the
`hcontract` slot-filler dispatch (§1.63(a)); statement change, grep `blueprint/src`.

> **L5b caveat (recorded so the L5b build doesn't re-discover it).** The simple-branch restate
> reuses `case_I_realization`'s `rigidContract_exterior_rank_transport_htransport` leg, which is
> **`hdef=0`-gated** — at `k>0` it doesn't apply, so the *simple* all-`k` Case-I arm (Lemma 6.3 at
> `k>0`) **also** needs this (d) brick's GP variant for its surviving block, not a mechanical
> `0→k` substitution. §1.63(d)'s "V6-b, expected mechanical" flag **under-scoped** L5b: re-route
> through the (d) brick (GP variant via `_of_le_finrank`), not "substitute `k` for `0`". (This
> "buildable, GP variant" framing itself later read as an **understatement** — P≈2 vs. the
> realized P≈3, see §1.65/§1.66.)

*Verification:* **V6-a** re-aimed at (d)'s correspondence form (§1.63's "reuse the splice-glue
decomposition" is superseded — that's the `def=0` rigidity instance); **V6-b** re-scoped (not
mechanical, needs the (d) brick's GP variant). Neither research-shaped.

### 1.65 The L5b design-pass — decomposing the all-`k` simple GP restate `case_I_realization_all_k`: the V6-b leaf is a genuinely-new `def = k > 0` *exterior-projected* rank-transport (a real brick, **P≈3**, NOT a clean assembly of landed pieces), because every landed projected-row tool is `0`-dof-gated; the leaf is pinned by signature but its internal route (route-1 projected rank-polynomial mirror vs route-2 pulled-back full-span + `hInj`) is left as a flagged open decision for the V6-b build, since both converge on needing a deficiency-aware analogue of the whole rigid U3a/U3b/U2-proj + rank-polynomial-proj chain (2026-06-13)

> ⚠️ **Route resolution: §1.66 (2026-06-13) found route 2 dead and the producer's vehicle wrong.** (a)/(f)
> below stand unchanged. (c)'s V6-b `P≈3` rating stands (its open route resolves to route 1, not the soft-
> recommended route 2). (b)'s "L4b-2 splice pattern" target-shape claim is **inverted** by §1.66(c)/(f): the
> producer instead mirrors the rigid coupler, never touching the splice brick. (d) and (g) are superseded by
> §1.66(e)/(g)'s corrected signature and build-leaf cut; (e)'s outer signature stands, its body is re-aimed
> at §1.66(f). The route-2 leaf `exists_rankPolynomial_of_IH_relabel_linking` (built per (g)) is dead under
> §1.66; its shared core `finrank_span_rigidityRows_ofNormals_relabel_eq` survives (route 1 reuses it).

**Citation.** Katoh–Tanigawa 2011, *Discrete Comput. Geom.* **45**, 647–700; **Lemma 6.3**, §6.2, p. 673
(the simple Case-I arm `case_I_realization` restates), with the `k > 0` surviving-block rank routed through
**Lemma 5.1** (the [29] White–Whiteley pin-a-body fact, p. 668, landed as `finrank_pinnedMotions_add_screwDim`),
exactly as §1.64 settled for the non-simple (Lemma 6.2) arm.

**(a) The row-104 BLOCK's diagnosis, re-verified correct but under-specified.** Confirmed against the landed
source: `case_I_realization`'s surviving block routes through `rigidContract_exterior_rank_transport` +
`exists_rankPolynomial_of_rigidOn_linking_set_proj` (both `hdef = 0`-gated), and the final coupler
`hasGenericFullRankRealization_of_couple_blockTriangular_ofNormals_set` is doubly `0`-dof-gated (hard `hdef = 0`
gate, plus `hsc_proj_indep` demands the *full* `D(|sc|−1)` projected surviving rank, not `D(|sc|−1) − k`) — so
the all-`k` restate needs a different surviving-block route, confirmed. Under-specified: the landed **L5a-ii**
machinery (`hInj` + `hingeRow_collapseTo_comp_extProj_eq`, both placement-free) already sidesteps the per-edge
`panelRow` correspondence the BLOCK worried about; the real residual gap is narrower (see (c)).

**(b) [Target shape — INVERTED by §1.66(c)/(f)].** Argued `case_I_realization_all_k` should follow the L4b-2
GP-builder pattern (`case_cut_edge_realization_gp`'s splice analogue): IH at deficient rank → per-leg
deficiency-aware rank polynomials → a fresh combined alg-indep seed `q₀` → the L5a-i splice brick's block-sum
lower bound → B2 closes by antisymmetry — reasoning that the L5a-i splice brick (`hFH_le`/`hFH_ker`/
`hFc_surv_le`/`hInj`, `D`-abstract and rigidity-free) was built general-rank precisely so this pattern
transfers. **§1.66 found the opposite:** the producer instead mirrors the rigid `case_I_realization`'s
block-triangular coupler directly, and never uses the splice brick at all.

**(c) The genuine residual gap — the V6-b leaf, rated `P≈3` (a real brick, not assembly).** Threading the
splice brick, the H-leg and brick assembly reuse landed pieces cleanly; the **one** piece with no landed
precedent is the surviving-block rank input to the brick at the fresh generic seed — discharging `Fc` with
both (i) `finrank (span Fc.rigidityRows) ≥ D(|sc|−1) − k` and (ii) `hFc_surv_le : (span Fc.rigidityRows).map
Dmap ≤ (span F.rigidityRows).map Dmap` **simultaneously** at a seed compatible with `F = ofNormals G G.endsOf
q₀`. Genuinely new because of the collapsed/uncollapsed normal mismatch crossed with deficiency: `Fc`'s
surviving extensors must be the *pulled-back* `q₀`-extensors for `hFc_surv_le` to discharge (the non-simple
producer's mechanism), but that `Fc` sits at a *degenerate placement*, not the IH's own generic seed, so its
deficient rank does not transfer for free — the rigid analogue's whole U3a/U3b/U2-proj + rank-polynomial-proj
chain is `hdef=0`/`hrig`-gated end to end, with **no deficient analogue in tree**. Rated `P≈3` — genuinely-new
linear algebra needing its own brick, the same tier as the L5a-i brick; needs NO motive/IH change.

Two candidate routes were left open: **route 1** (rebuild the `_proj` chain deficiency-aware: a new `_proj`
extractor + `_proj` rank polynomial + relabel transport, mirroring the rigid chain step-for-step) vs. **route 2**
(reuse the landed L5a-ii `hInj` + the landed full-span L4b-1 rank polynomial on the pulled-back `Fc`, needing
only the relabel transport as new content) — soft-recommended as the smaller surface. **§1.66 found route 2 is
a dead end** (a mechanism mismatch, not a missing lemma); route 1 is the one that builds.

**(d) [SUPERSEDED — see §1.66(e)].** Pinned the V6-b leaf's *interface* only (a `Q`-non-root seed gives the
surviving block its deficient rank `D(|sc|−1) − k` under the exterior projection, the deficient sibling of the
rigid coupler's `hsc_proj_indep`), leaving the conclusion's exact shape (`_proj`-form for route 1, or a split
full-span rank + `hInj` for route 2) as an open design slot. §1.66(e) resolves it to the `_proj` form.

**(e) The all-`k` GP producer signature — outer shape unaffected by §1.66, body re-aimed there.** All-`k`
`case_I_realization_all_k` (`{k : ℤ}`, the conditioned-pair IH the L9 spine threads, `hcSimple` as the dispatch's
positive-branch output, simple branch concluding the GP conjunct) — §1.66(f) confirms this outer signature
survives unchanged; the body originally sketched here (H-leg rank polynomial + V6-b leaf + fresh seed + the
L5a-i splice brick's block-sum + B2) is corrected there to assemble the rigid coupler instead. The 6.5 sub-arm
stays red → L8 regardless. Statement change vs. the landed `case_I_realization` → blueprint statement-grep gate.

**(f) The `hcontract` dispatch (plumbing, unaffected by §1.66).** The final assembly filling L9's `hcontract`
slot, unchanged in shape from §1.63(a) / the landed `theorem_55_d3` `hcontractGP` dispatch: `by_cases G.Simple`
→ simple branch dispatches on whether some proper rigid subgraph has a simple contraction, positive →
`case_I_realization_all_k`, negative → the `h65` carry; non-simple → the landed `case_I_realization_nonsimple`
(L5a-ii). No new math once `case_I_realization_all_k` lands — per `CLAUDE.md` *"wiring is a deliverable"*, its
own checklist leaf, not a commit-message phrase.

**(g) [SUPERSEDED — see §1.66(g)].** Cut L5b into three leaves: L5b-i the V6-b brick (d), L5b-ii the GP producer
(e) as a splice-brick analogue of `case_cut_edge_realization_gp`, L5b-iii the `hcontract` dispatch (f, **`P≈1`**,
unchanged by the §1.66 re-cut). Once the route-2 L5b-i leaf was found dead, §1.66(g) re-decomposes L5b-ii into
four leaves; L5b-iii survives as-is.

### 1.66 The L5b-ii route resolution — `hFc_surv_le` is a DEAD END for the GP simple producer (the splice brick is the wrong vehicle, not a discharge gap): route 1 (`_proj`-coupler mirror) is the only viable route, route 2's L5b-i leaf `exists_rankPolynomial_of_IH_relabel_linking` is SUPERSEDED (dead, no consumer — leave harmless); the all-`k` simple Case I must mirror the LANDED rigid `case_I_realization` (the block-triangular row-counting coupler `hasGenericFullRankRealization_of_couple_blockTriangular_ofNormals_set`, NOT `le_finrank_span_rigidityRows_of_splice`), so the V6-b leaf is re-pinned as the deficient `_proj` surviving-row independence the coupler's `hsc_proj_indep` consumes; no motive/IH change; re-decomposed L5b-ii → three buildable leaves (2026-06-13)

> **Docs-only design pass, every load-bearing decl re-verified against the LANDED Lean this pass** (the
> §1.65 soft-rec for route 2 + the BLOCK both came from prose-trust; this pass opened each `def`/`theorem`
> and traced the *mechanism*, not the conclusion). **CaseI builds green (exit 0) at HEAD `6d74065`.** No
> `.lean`/`.tex` edits this pass.

**Citation.** Katoh–Tanigawa 2011, *Discrete Comput. Geom.* **45**, 647–700; **Lemma 6.3** §6.2 p. 673 (the
simple Case-I arm), the `def = k > 0` surviving-block rank routed through **Lemma 5.1** (White–Whiteley pin-a-body,
p. 668; landed as `finrank_pinnedMotions_add_screwDim` / its corank consequence the rigidity-free `injOn` core).

**(a) The decisive finding — `hFc_surv_le` is undischargeable for the GP producer because it is the WRONG
mechanism, not a missing lemma.** The non-simple producer discharges `hFc_surv_le` (`r' ∈ Fc.hingeRowBlock e' ⟹
r' ∈ F.hingeRowBlock e'`, since `hingeRowBlock e = (span {supportExtensor e})^⊥`) only because it holds **iff
`F.supportExtensor e'` is parallel to `Fc.supportExtensor e'`**, and that producer hand-builds `F` to *copy*
`Fc`'s extensor on surviving edges, concluding only the bare motive. The GP conjunct instead forces
`F = (ofNormals G G.endsOf q₀).toBodyHinge` at a fixed seed: on a **crossing edge** of `H` that survives (one
endpoint inside `V(H)∖{r}`, generic whenever `H` has boundary edges), `F`'s support-extensor is built from the
point-pair `(u,v)` while every contraction framework's is built from `(r,v)` (the collapsed normal at `r`, not
`u`) — extensors of different point-pairs, generically **non-parallel**. So `hFc_surv_le` fails for the GP `F`
not for want of a lemma but because the two frameworks genuinely disagree on the surviving-edge hinge constraint
once `F` is pinned to a clean generic seed. The splice brick is the non-simple producer's vehicle (bare motive,
`F` copies `Fc`); it is the **wrong vehicle** for the GP producer — a mechanism mismatch, not a discharge gap.

**(b) Why route 2 cannot be repaired by a degenerate seed.** The BLOCK's candidate — realize `Fc` at
`degeneratePlacement r V(H) q₀` so the collapse reconciliation discharges `hFc_surv_le` — does not change the
obstruction: at that placement `Fc`'s support-extensor is still built from `(r,v)`, still non-parallel to `F`'s
`(u,v)`-built one. The only fix is to hand-build `F` to copy `Fc` (the non-simple route), which forfeits the GP
conjunct. Route 2 is a genuine dead end for L5b-ii.

**(c) The viable route — route 1, the `_proj`-coupler mirror, the deficiency-aware twin of the LANDED rigid
`case_I_realization`.** The rigid `case_I_realization` **does not use the splice brick at all** — it routes
through the block-triangular coupler `hasGenericFullRankRealization_of_couple_blockTriangular_ofNormals_set`,
exhibiting `D(|V|−1)` independent rigidity rows of the *single* framework `F = ofNormals G ends q₀` itself: the
H-block rows (vanishing under `Dmap`) `⊔` the exterior-projected surviving rows. The surviving block enters as
`hsc_proj_indep`: a rank-polynomial-gated witness that `F`'s **own** surviving panel rows are projected-
independent of size `≥ D(|sc|−1)` — a statement about `F`'s rows, **never** a span-containment with `Fc`. The
coupler never needs `Fc.supportExtensor = F.supportExtensor`, because it reads everything off `F`. This is the
route the deficient case mirrors, lowering the projected rank target to `D(|sc|−1) − k` and weakening
"independent" to "rank `≥`". The rigid chain feeding `hsc_proj_indep` (`rigidContract_exterior_rank_transport` →
U3a `hasGenericRealization_transport_relabel` (`hdef`-gated) + U3b's rigid `_proj` extractor (`hrig`-gated) + U2)
is entirely built at a degenerate-placement *witness*, not the producer's realized seed — dissolving the BLOCK's
apparent "seed conflict".

**The deficient analogues of every `hdef=0`/`hrig` link are already landed or near-mechanical** (why route 1 is
`P≈3`, a real brick, not research-shaped): U3a → the **landed** L5b-i shared core
`finrank_span_rigidityRows_ofNormals_relabel_eq` (the one piece §1.65(c) flagged as the real uncertainty,
already in tree from route 2, reused here — see (d)); U3b's `injOn` core → the **landed** L5a-ii rigidity-free
`injOn_extProj_dualMap_rigidityRows_of_inter_eq_singleton`; U3b's un-projected extractor → the **landed** W6e
`exists_independent_panelRow_subfamily_of_le_finrank`; U2 is already rigidity-free, reused verbatim. The
genuinely-new step is a **deficient `_proj` extractor** (W6e composed with the rigidity-free `injOn` core) plus
a **deficient `_proj` rank polynomial** mirroring the rigid one — ~2 new lemmas, a real but bounded brick. No
motive/IH statement-level change: route 1 produces the same conclusion through the same coupler the rigid arm
uses; only the surviving-block rank input is deficiency-aware.

**(d) Disposition of the landed L5b-i route-2 pieces.** Two decls landed for route 2:
`finrank_span_rigidityRows_ofNormals_relabel_eq` (the shared core) is **reused by route 1** as its U3a
relabel-transport analogue — keep, both routes need it. `exists_rankPolynomial_of_IH_relabel_linking` (the
route-2 leaf, producing the full-span rank the **splice brick** consumes) is **superseded (dead) for L5b**:
verified no consumer in tree. Recommendation: leave it harmless (axiom-clean, build-green, its blueprint node
a truthful fact) and delete at the L5b close once route 1 lands and it is confirmed not resurrected — deleting
now would strand its green blueprint node mid-build. Its shared-core dependency survives regardless.

**(e) The V6-b leaf re-pinned for route 1 (the deficient `_proj` surviving-row independence).** Resolves §1.65(d)'s
open design slot to the **`_proj`-form** (route 1), not the full-span form (route 2). Two new decls, the
`_le_finrank` siblings of the rigid `_proj` pair: `BodyHingeFramework.exists_independent_panelRow_subfamily_of_
le_finrank_proj` (the extractor — the rigid extractor's body verbatim with `hrig`→`hN` a rank input and the
rigidity-gated `injOn` swapped for the L5a-ii rigidity-free `hinter` core, no separate rigidity hypothesis) and
`PanelHingeFramework.exists_rankPolynomial_of_IH_relabel_linking_set_proj` (the rank polynomial — from the
contraction IH on `Gc.map f`, a nonzero `Q` whose non-roots give the coupler's `hsc_proj_indep` directly: the
`(extProj V(H)).dualMap`-projected surviving rows of `ofNormals Gc ends q` independent of size `≥ D(|sc|−1) −
k'`, mirroring `rigidContract_exterior_rank_transport_htransport` at the deficient leg via the shared core +
the new extractor + U2). Blueprint mints **one** new node `lem:rank-polynomial-IH-relabel-proj` (beside the
now-superseded `lem:rank-polynomial-IH-relabel`).

**(f) The producer `case_I_realization_all_k` re-aimed at the coupler (the L5b-ii rewrite).** Mirror the rigid
`case_I_realization`, **not** `case_cut_edge_realization_gp`. Signature unchanged from §1.65(e) (all-`k`, the
conditioned-pair IH, simple branch concluding the GP conjunct); the **body** is the rigid arm's body with the
surviving-leg input swapped: H-leg rigid rank polynomial `exists_rankPolynomial_of_rigidOn_linking_set`
(unchanged) + the deficient `_proj` rank polynomial (e) for the surviving block (replacing the rigid
`rigidContract_exterior_rank_transport` chain), fed to the coupler with **`hdef` replaced by the deficient
surviving target** — the one signature subtlety: the landed coupler hard-codes `hdef : G.deficiency n = 0` and
demands the *full* `D(|sc|−1)`, so **the coupler itself needs a deficiency-aware restate**
(`hasGenericFullRankRealization_of_couple_blockTriangular_ofNormals_set_kdof`, lowering `hdef=0`→
`G.deficiency n = k`, target `D(|sc|−1)`→`D(|sc|−1)−k`, conclusion to `D(|V|−1)−k`) — a third new decl,
mechanical (row-counting + B2-antisymmetry arithmetic restated with `−k`). The 6.5 sub-arm stays red → L8.
Statement change vs. the landed `case_I_realization` → grep `blueprint/src` per the structural-edit gate.

**(g) The re-cut L5b-ii build leaves (replacing the §1.65(g) L5b-ii single leaf).** L5b-i's route-2 leaf is dead
(the shared core and W6e/`injOn`/U2 survive); the remaining work re-cuts into four leaves + the unchanged
dispatch, all buildable:

* **L5b-ii-a** — the deficient `_proj` extractor (e, first decl). **`P≈2`** — the rigid extractor's body
  verbatim with two landed swaps. First concrete L5b-ii commit. No blueprint node (churn-prone `_proj` infra).
* **L5b-ii-b** — the deficient `_proj` rank polynomial (e, second decl), assembling L5b-ii-a + the shared core
  + U2. **`P≈3`** — the genuinely-new assembly, **the V6-b leaf in its corrected (route-1) form**. Mints
  `lem:rank-polynomial-IH-relabel-proj`.
* **L5b-ii-c** — the deficiency-aware coupler restate (f, the `−k` lowering). **`P≈2`** (mechanical). May fold
  into L5b-ii-d if small.
* **L5b-ii-d** — `case_I_realization_all_k` (f): the producer, assembling the H-leg rigid polynomial +
  L5b-ii-b + L5b-ii-c. **`P≈2`** (a clean assembly mirroring the rigid arm's body). Mints
  `lem:case-I-realization-all-k`. Statement-grep gate before commit.
* **L5b-iii** — unchanged from §1.65(g): the `hcontract` dispatch. **`P≈1`** (plumbing). Updates
  `lem:case-I-dispatch`; the 6.5 sub-arm stays red → L8.

**Route-1 build adds three new decls** vs. the route-2 soft-rec's "reuse L5b-i + splice brick" — more Lean
surface than §1.65 projected, but the only surface that produces the GP conjunct (route 2 cannot). The
§1.64(c)/§1.65(c) flag "do not over-commit the internal route in a pin" did its job: the route was not
committed, the L5b-i build followed route 2 *as a lemma* (sound, reused), and this pass corrects the
*producer's* route before any producer Lean was written on the wrong foundation — avoiding the L5a-i
boundary-pair lesson (a wrong-for-purpose green commit on master).

### 1.67 The L6 signature pin — Lemma 6.8, the `k > 0` split (`hsplitPos`): the `hsplitPos` producer pins against the SETTLED §1.56(c) all-`k` IH; the eq. (6.12)–(6.17) placement reuses the landed `case_II_placement_eq612` but at a DEFICIENT `(k−1)`-dof IH, so its one rigidity-gated step (the OLD block) needs the deficiency-aware swap (`_of_rigidOn_linking` → `_of_le_finrank` at rank input `N := D(|V(Gv)|−1)−(k−1)`) — V7 RESOLVED: the W-suite (the `t=0` certify-then-rebase, `exists_shear_linearIndependent_pair`, `caseIIICandidate_exists_good_shear`) transfers WHOLESALE because it is rank-driven, not rigidity-driven, and L6 is STRICTLY SIMPLER than the `k=0` Case III (the deficient IH already supplies the full target rank `D(|V|−1)−k`, so NO Claim-6.11/6.12 redundant-row machinery, NO `h622`); no motive/IH change (2026-06-13)

**Citation.** Katoh–Tanigawa 2011, *Discrete Comput. Geom.* **45**, 647–700; **Lemma 6.8**, §6.3,
p. 677–680 (eqs. 6.11–6.17, the Lemma-5.2 nonparallel conversion); the degree-2 vertex is **Lemma
4.6**, the dof-decrement split-off is **Lemma 4.8**. KT states the `k=0`-vs-`k>0` contrast
verbatim (p. 680): at `k=0` the placement gives only `rank ≥ 5+6(|V∖v|−1) = 6(|V|−1)−1` ("does not
complete the proof"), whereas Lemma 6.8's `k>0` case "obtains the desired rank" — the V7 crux this
pin verifies.

**The slot.** L2's `hsplitPos` slot (`minimal_kdof_reduction_all_k`, §1.59(a)) at the conditioned
pair `Pc` (§1.56(b) M4): `G` minimal-`k`-dof, `0<k`, `3≤|V(G)|`, 2-edge-connected, no proper rigid
subgraph, all-`k` IH at smaller graphs ⟹ `Pc G`. The bare conjunct is free (G0
`simple_of_isMinimalKDof_of_noRigid` + M4-forgetful `hasPanelRealization_of_generic`, as L5
§1.66); L6 need only build the GP conjunct `HasGenericFullRankRealization`. `htec` is carried but
not consumed by the rank argument (the producer re-derives `G_v^{ab}`'s simplicity from `hnoRigid`
directly, KT 6.7(ii), rather than via 2EC).

**(a) The pinned producer.** `PanelHingeFramework.case_II_realization_all_k` (CaseI.lean, beside
`case_III_realization`, its `k=0` sibling): under `hD`/`hn` (ambient, matching
`case_I_realization_all_k`/`case_III_realization`) and `hfresh` (a fresh split-off edge, as
`case_III_realization` carries for the splitting case), the slot's `hG`/`hk`/`hV3`/`htec`/
`hnoRigid`/`hIH` conclude `HasGenericFullRankRealization 2 n G`.

**(b) The construction (KT eqs. 6.11–6.17, reuse verified against the landed Lean).** (1) `exists_
degree_eq_two` (KT 4.6) + `splitOff_isMinimalKDof_of_pos` (KT 4.8) give a degree-2 `v`,
`N_G(v)={a,b}`, and `G_v^{ab} := G.splitOff v a b e₀` minimal-`(k−1)`-dof, simple (KT 6.7(ii)).
(2) The all-`k` IH at `(k−1, G_v^{ab})` gives a **deficient** generic realization, rank
`D(|V∖v|−1)−(k−1)` (eq. 6.11) — the one substantive departure from the `k=0` Case III's *rigid*
IH; transversality of the IH `ab`-hinge comes from the realization's general position. (3) The
landed `case_II_placement_eq612` (the eq.-6.12–6.17 placement brick) needs a **deficiency-aware
variant** `case_II_placement_eq612_kdof`: its body *verbatim* with the OLD block's `hrig` +
`exists_independent_panelRow_subfamily_of_rigidOn_linking` swapped for the rank-input
`exists_independent_panelRow_subfamily_of_le_finrank` (W6e, GenericityDevice.lean, NO rigidity) at
`N := D(|V(Gv)|−1)−(k−1)`, and the count arithmetic (`D(|V(G)|−1)−1 = (D−1)+D(|V(Gv)|−1)`) shifted
by `k−1`; everything else (the NEW `e_b`-block, pin-a-body split, transversality) is
rigidity-agnostic and copies unchanged. (4) The parallel-candidate rank `≥ D(|V|−1)−k` converts to
nonparallel by the **same certify-then-rebase W-suite the `k=0` Case III already uses**
(`exists_independent_panelRow_subfamily_of_le_finrank` re-extraction +
`setOf_not_shear_linearIndependent_subsingleton` (uses only `hgab`) +
`caseIIICandidate_exists_good_shear`'s `t*≠0`) — rank-driven, not rigidity-driven, so it transfers
wholesale.

**(c) Why L6 is strictly simpler than the `k=0` Case III.** At `k=0` the IH is rigid, so eq. 6.12
gives `(D−1)+D(|V∖v|−1) = D(|V|−1)−1` — one row short of target, closed only by the
Claim-6.11/6.12 redundant-`ab`-row machinery (KT's largest proof, carried by
`case_III_candidate_dispatch`'s `h622lb`). At `k>0` the deficient IH gives exactly
`(D−1)+[D(|V∖v|−1)−(k−1)] = D(|V|−1)−k` — the target, no shortfall. So L6 needs no `h622`, no
candidate dispatch over `D` candidates, no redundant-row extraction — only the eq.-6.12 placement
(at the deficient IH) + the single-candidate shear conversion.

**(d) Verification items.** V7 RESOLVED (the W-suite transfers wholesale; the deficiency-aware
`_kdof` swap is the one delta, near-mechanical per the V6-b/L5b-ii-a precedent). No motive/IH
change. Two residual **build-time** checks (not blockers): **(b1)** the exact landed lemma for
"`G_v^{ab}` simple from `hnoRigid`" (KT 6.7(ii)) — expected the `splitOff`-simplicity +
`loopless_of_isMinimalKDof` facts the `k=0` dispatch already uses; **(b2)** whether
`case_II_placement_eq612`'s abstract `Gv` parameter is fed `G_v^{ab} = G.splitOff v a b e₀` (yes —
KT's `(G_v^{ab},q)` is the split-off, reproducing `q(ab)` via
`panelSupportExtensor_add_smul_right`) vs `G.removeVertex v`; confirm the selector wiring at the
build (the rigid dispatch threads both via `hle : Gv.IsLink → Gab.IsLink`).

**(e) The L6 slice cut.** Mirrors L5b-ii (§1.66(g)): **L6a** `case_II_placement_eq612_kdof`
(`P≈2`, the rigid brick's body verbatim with the two (b)(3) swaps; no blueprint node, the `_kdof`
infra sibling of `case_II_placement_eq612`); **L6b** `case_II_realization_all_k` (the (a)
producer, `P≈3`, the genuinely-new assembly), mints `lem:case-II-realization` restating it green
at the `k>0` content (statement-grep gate — the `\lean{...}` survives the flip). The 6.5 sub-arm
does not enter L6 (it is the `hcontract`/Case-I arm, carried as `h65` → L8); L6 is purely the
`hsplitPos` splitting case. Buildable, no motive/IH change.

---

> **[SUPERSEDED — dead legacy stub, pre-dating every `### 1.xx` sub-section, 2026-07-09 collapse.]**
> This was the original Phase-22 opening recon's "per-case producer structure / risk / one-line
> recommendation" stub (`## 3.`/`## 4.`/`## 5.`, nested under the still-open `## 1. Motive
> decision` — no `## 2.` was ever opened). Its own text already marked it superseded on
> 2026-06-07 ("Re-scoped … the real gap is narrower than this stub. Read §1.33 (A)/(B)"). Every
> codename it names (`N6a`, `N6-G1`/`G2`/`G3`, Track A/B) is now canonically documented in
> `notes/Phase22a.md` (+ `MolecularConjecture.md`/`DESIGN.md`/`TACTICS-QUIRKS.md`/
> `BlueprintExposition.md`), all of which cite the codenames directly, never this block by heading
> or section number — confirmed by a tree-wide grep (2026-07-09) finding zero external citers of
> this block. Collapsed hard rather than given the anchor-preserving per-letter treatment; see
> §1.33 for the live successor recon.

---

### 1.68 The Phase-22j design — the shared span-transport placement abstraction (the Case-II/III/Lemma-6.8 analogue of the landed Case-I splice brick): a recon-verified **TWO-brick family**, not one — **Brick A** `le_finrank_span_rigidityRows_of_pinned_placement` (NEW, span-level rank, what L6b + 22k's Case III consume) + **Brick B** `case_III_old_new_blocks` (the EXISTING literal-`panelRow` device-feed shape, kept); Case I stays on its splice brick + coupler (contraction = `extProj`-projected-column geometry vs split = `single v` pin-a-body geometry — KT's own Lemma 6.2 vs 6.8 split); common cause of the L6b ≈1010-line inlining = the placement bricks key their conclusion on *literal* `G.rigidityRows` membership (forcing `Gv ≤ G`), but every real reduction graph (collapse / `splitOff` / relabel) lands rows only in `span(G.rigidityRows)`; verified read-only against the landed signatures (2026-06-14)

**(a) The common cause — the literal-brick anti-pattern.** `case_II_placement_eq612` (CaseI.lean:3520)
and the now-dead `case_II_placement_eq612_kdof` both take `hGv : Gv ≤ G`, used in exactly one place —
the OLD-block membership step `IsSubgraph.isLink_iff hGv`. Every real reduction graph is
**non-subgraph** (Case I's `rigidContract` collapse, L6b's `splitOff`, Case III's `removeVertex`+relabel),
so OLD rows land only in `span(G.rigidityRows)` and the literal brick fits no caller — each producer
re-derives the placement instead. Case I already has the correct span-level shape
(`le_finrank_span_rigidityRows_of_splice`, RigidityMatrix.lean:3213); Case II/III/Lemma-6.8 never got
the analogue.

**(b) The TWO-brick verdict.** Two irreducible conclusion shapes, not one brick:
- (A) span-rank: `N ≤ finrank(span G.rigidityRows)` — L6b's `hN_FG`/`hrank_lb`, Case III's
  `case_III_rank_certification`, whose interface is already span-transport and does not consume
  `case_III_old_new_blocks`.
- (B) literal device-feed: an independent family of literal `G.panelRow`s, consumed by
  `hasFullRankRealization_of_independent_panelRow_index` (GenericityDevice.lean:355), which requires
  literal rows — `case_III_old_new_blocks`, CaseI.lean:5571.

They share the block-triangular core `linearIndependent_sum_pinned_block` (RigidityMatrix.lean:1337)
and the `q₀`-shear front matter, but (A) can't return literal rows post-reduction and (B) can't be
span-transport — irreducibly different.

**(c) Brick A — `le_finrank_span_rigidityRows_of_pinned_placement`** (RigidityMatrix.lean, beside the
splice brick; + an `_augment` variant via `linearIndependent_sum_pinned_block_augment` for Case III's
`+1`). Span-level, framework-agnostic; interface: a NEW block independent through `single v`'s column
(`hnewpin`) + an OLD block vanishing on `v`'s column (`hold`), independent (`holdindep`), in
`span F.rigidityRows` (`hold_span`), plus `hnew_span` for the NEW rows ⇒
`Nat.card ιn + Nat.card ιo ≤ finrank(span F.rigidityRows)`. Proof = L6b's `hrank_lb` skeleton lifted
out (`linearIndependent_sum_pinned_block` → `finrank_span_eq_card` → `Submodule.finrank_mono`); no new
math — the genuinely-new content is each caller's `hold_span` discharge (d). Arithmetic closes via
`hNpD` (`N + (D−1) = D(|V|−1) − k`) for L6b and the `_augment` `+1` for Case III.

**(d) Per-case transport-discharge map** (how each caller proves `hold_span`):
- **Lemma 6.8 / L6b** (`splitOff`): the `e₀ = e_a + e_b` row decomposition `he₀_rows_mem` for the fresh
  edge + the orientation-reconciling `hso_span` for non-`e₀` rows. **GENUINELY NEW** (≈130 lines).
- **Case III all-`k` / 22k** (`removeVertex`+relabel): already isolated as the `hρGv`/`hwmem`
  span-interface `case_III_rank_certification` consumes — mechanical reuse; 22k's new content is the
  rank input (V8), not the placement.
- **Subgraph (`Gv ≤ G`, TRIVIAL):** `hold_span := Submodule.subset_span ∘ panelRow_mem_rigidityRows`,
  link via `IsSubgraph.isLink_iff hGv` — the rigid `case_II_placement_eq612`'s current membership step.
- **Case I (collapse): N/A — does not use Brick A** (see (e)).

**(e) Case I stays separate — verified, not a deficiency.** Case I's GP route uses the coupler
`hasGenericFullRankRealization_of_couple_blockTriangular_ofNormals_set`, whose surviving-block input is
**`(extProj sH).dualMap`-projected** rank (collapse → projected-column geometry), not an unprojected
`span F.rigidityRows` containment. Brick A's `single v` pin-a-body core is the *splitting* tool;
collapse needs the `extProj` tool — KT's own Lemma 6.2 vs 6.8 distinction, not a missing unification.

**(f) Retrofit & blueprint impact.** Brick A subsumes L6b's rank halves (S4) and is what 22k's Case III
consumes. Brick B (`case_III_old_new_blocks`) is **kept** (different conclusion shape); its
deficiency-aware generalization is **S3, deferred to 22k**. **L6a (`case_II_placement_eq612_kdof`)
retires** (dead, no live caller — `case_II_realization_all_k` inlines the steps). The rigid
`case_II_placement_eq612` **must stay untouched** — the `\leanok` witness for
`lem:case-II-realization-placement`, `\uses`'d across `case-iii.tex` (22k's Case-III chain); it is
**not** re-routed through Brick A. *Why not (the "option (i)" shape error, settled 2026-06-14):* Brick
A's conclusion is shape (A), a bare finrank bound that discards the subfamily consumed internally;
`case_II_placement_eq612`'s conclusion is shape (B), exposing a literal independent `panelRow`
subfamily `∃ s` (plus `supportExtensor e_a ≠ 0`) — feeding through Brick A loses the `∃ s`. The
alternative chain Brick A → `exists_independent_panelRow_subfamily_of_le_finrank` (W6e,
GenericityDevice.lean:718) recovers shape (B) but is **possible-but-net-negative**: a double
extraction (Brick A discards what W6e re-extracts) yielding a less-structured `s`, while still needing
the `q₀`-shear front matter for the `supportExtensor` conjunct and W6e's transversality — so the rigid
decl stays on its current proof. One new blueprint node `lem:rigidityRows-pinned-placement-rank-add`
(beside `lem:rigidityRows-splice-rank-add`).

**(g) Slice plan + open risks** (full layer plan in `notes/Phase22j.md`): S1 build Brick A
(+`_augment`) → S2 blueprint node → S4 refactor L6b onto Brick A, extracting `he₀_rows_mem` as the
named `hold_span`-discharge helper → S5 retire L6a (delete-only; the rigid `case_II_placement_eq612`
left untouched, see (f)) → cleanup bundle (drop the L6b heartbeats/`longLine` suppressions; delete
dead code; refresh the §C long-proof note). Open risks: **(i)** Brick A's `Nat.card`/`Fintype`
instance resolution across call sites (L6b's `Set`-subtype indices vs W6b's `Fin`) — RESOLVED cleanly
via the standard `Nat.card_eq_fintype_card`+`Fintype.card_sum` bridge; **(ii)** S4 must preserve the
`e₀`-decomposition's orientation case-split when extracted (low-medium; S3's `_of_line`-preservation
risk is 22k's, not 22j's).

### 1.69 The L7 signature pin — the Case-III rewire, `h622` *derived* from the all-`k` IH (`hsplitZero`): `case_III_realization` restates to carry the all-`k`-conditioned IH (mirroring 22i's reduction-case producers), the IH at the nested `k'`-dof `G_v` (`k' ≤ D−2`, `lem:case-III-gap3-minimalKDof` green) supplies the eq.-(6.22) lower bound `h622lb`; V8 RESOLVED — buildable, no motive change: UNLIKE L6 (whose IH seed coincides with the realization's, so it reads the bound off directly), L7's nested `G_v` realization is at its OWN seed while `h622lb` is wanted at the split realization's DIFFERENT seed, so the rank transfer IS the landed deficiency-aware rank-polynomial idiom (§1.62, `exists_rankPolynomial_of_le_finrank_linking` + footnote-6 non-root, NOT the `def=0`-only seed-rank bridge), with one genuinely-new sub-leaf (V8-a / L7a, P≈3): the non-relabel (`f=id`) rank-polynomial brick mirroring `exists_rankPolynomial_of_IH_relabel_linking`; no motive change beyond the §1.56 all-`k` IH restate (2026-06-15)

**Docs-only design pass (opus, 2026-06-15).** Every load-bearing decl verified against the landed
source (the post-22j 5-file chain: CaseIII.lean, CaseII.lean, CaseI.lean, GenericityDevice.lean,
ForestSurgery.lean, PanelHinge.lean) and KT 2011 §6.4.1 read end-to-end against the PDF (pp. 684–686:
Claim 6.11, the nested IH (6.1) at `G_v`, eqs. (6.22)/(6.23); p. 680's `k=0` contrast confirming the
redundant-`ab`-row machinery exists only because the `k=0` IH is rigid). No `.lean`/`.tex` edits this
pass.

**The slot the L7 producer fills.** L7 is the `hsplitZero` arm of `theorem_55_generic` — the landed
22h Case-III producer, restated. It is the `k=0` sibling of L6 (`case_II_realization_all_k`, the
`k>0` `hsplitPos` arm): both reduce by splitting off a degree-2 vertex, both reuse the eq.-(6.12)
placement; the difference is that the `k=0` IH at the split-off `Gab` is **rigid** (`def=0`), giving
only `D(|V|−1) − 1` — one row short (KT p. 680), so `k=0` Case III alone runs the whole Claim-6.11/6.12
redundant-`ab`-row machinery (already landed, 22h, green-modulo `h622lb`). L7's only job is to
**discharge `h622lb`** by an all-`k` IH application at the nested `G_v`.

**(a) The corrected `case_III_realization` signature.** CaseIII.lean's landed `case_III_realization`
restates two-fold: **drop the `h622` carry** and **promote the `k=0` IH to the all-`k` IH** (the
§1.56(c) motive shape — the **conditioned pair** `Pc` (GP-if-simple ∧ bare), identical to
`case_I_realization_all_k`'s/`case_II_realization_all_k`'s `hIH`; L7 consumes its `.1` (GP) arm at
`G_v` simple). Everything else (`hD`/`hfresh`/`hG`/`hV3`/`hnoRigid`/`hSimple`, the conclusion) is
unchanged; `G` itself stays `IsMinimalKDof n 0` (L7 is the `hsplitZero` slot — the all-`k`-ness is
needed only for the *nested* IH at `G_v`). **Consequential caller change:** since the `k=0`-only IH
cannot supply `k'>0` instances, L7 forces the spine to be all-`k`-conditioned at the `hsplitZero`
slot — the §1.56(e) `theorem_55_all_k` spine (L9's job to wire in; L7 lands the producer alone). *Flag
F1 (not a blocker):* if the L7 commit must keep `theorem_55_d3` building before L9 lands, thread the
old `h622`-carrying shape via a thin wrapper until L9 swaps the spine — the same staging L5/L6 used.

**(b) The `h622lb` derivation (the heart of L7, KT eq. (6.22) at the nested IH).** `h622lb` is the
obligation that at any link-recording selector `ends` and any pairwise-LI, alg-indep seed `q`, the
`Gv := G − v` row span (w.r.t. `Gab := G.splitOff v a b e₀`, `m := |V(Gab)|`, `D := screwDim 2`) has
finrank `≥ D(m−1) − (D−2)`; the consumer instantiates this at the split realization `Q : Gab`'s own
`(ends, q) := (Q.ends, fun p => Q.normal p.1 p.2)`. Derivation: **(1)** `Gv` is minimal `k'`-dof with
`0 ≤ k' ≤ D−2` (`splitOff_removeVertex_minimalKDof`, green); **(2)** the all-`k` IH at `Gv` gives the
conditioned pair, whose `.1` (from `Gv.Simple`) supplies a realization `Q_v` at rank `D(m−1) − k'`;
**(3)** transfer that rank from `Q_v`'s own seed to the given `(ends, q)` via the deficiency-aware
rank-polynomial idiom (§1.62's `exists_rankPolynomial_of_le_finrank_linking` + the footnote-6 non-root
device) — **not** the `def=0`-only seed-rank bridge, which cannot handle `Gv`'s deficiency `k' > 0`.

**(c) V8 — RESOLVED to a leaf, with one flagged sub-leaf.** The transfer mechanism of (b)(3) is
settled: it is exactly the landed §1.62 rank-driven idiom, tolerant of deficient `Gv` (the `def=0`
seed bridge is its special case, not the right tool here — the blueprint proof of
`lem:case-III-nested-rank-lower` will need its "footnote-6 seed-transfer device" citation corrected to
the rank-polynomial extractor when this flips green). The genuinely-new sub-leaf (**V8-a / L7a**,
P≈3) is the selector mismatch: `Q_v`'s rank conjunct is at its own `(Q_v.ends, Q_v.normal)`, but the
obligation wants it at the given `(ends, q)`. Two adapters compose: a selector swap (`Q_v.ends ↔
ends`, both recording `Gv`'s links — `recordsLinks_agree_swap` + the motion-space-equality transport,
the `f = id` case of the landed relabel-core pattern) and the seed transfer of (b)(3). No landed
`map_id` reduction exists for `Gv.map id = Gv`, so the clean path is a dedicated non-relabel brick
mirroring the landed relabel one — near-mechanical, but the residual risk is whether it specializes
cleanly vs. needs a fresh selector-agreement argument.

**(d) The L7 slice cut (build order; ~2–3 commits).** **L7a** —
`PanelHingeFramework.exists_rankPolynomial_of_IH_linking` (CaseI.lean, beside the relabel sibling
`exists_rankPolynomial_of_IH_relabel_linking`): the non-relabel (`f = id`) deficiency-aware rank
polynomial (P≈3, V8-a); body is the relabel core specialized to `id` (a witness seed via the
selector-swap motion-space transport), then `exists_rankPolynomial_of_le_finrank_linking` at
`hN := le_refl N`; no blueprint node (churn-prone rank-polynomial infra, like its relabel sibling).
**L7b** — `case_III_realization` restated per (a), discharging `h622lb` via L7a's `N`-bound →
footnote-6 non-root → the `≥ D(m−1) − (D−2)` arithmetic (P≈2 assembly; the candidate-dispatch /
Claim-6.11/6.12 machinery is unchanged, since `case_III_candidate_dispatch` already consumes
`h622lb`); flips `lem:case-III-nested-rank-lower` green (correcting the seed-transfer citation per
(c)) and drops `h622` from `lem:case-III`'s pin — statement-grep gate before commit
(`lem:case-III`/`thm:theorem-55-d3-instance` state the `h622` carry, restate in the same commit). No
motive/IH change beyond the §1.56 all-`k` IH restate; no user adjudication needed (clause (ii)).

**(e) Scope + verification.** L7 discharges `h622` only — it does not touch `h65` (L8, the Lemma-6.5
`hcontract` sub-arm) or the spine wiring (L9 deletes the `h622`/`hsplit` carries from `theorem_55_d3`
by routing through `theorem_55_all_k`). The residual "`Gv` simple from `hnoRigid`" leaf (KT 6.7(ii))
is immediate from `hSimple` via subgraph (`L7`'s `Gv = removeVertex`, simpler than L6's `splitOff`
case); `Gv`'s deficiency `k'` may be `0` (then the IH leg is rigid and the transfer is the seed
bridge's `def=0` case) or `>0`, both covered uniformly by the rank-polynomial route (no case split).
Shape-match confirmed against the landed source: the IH's `finrank` *equality* conjunct yields the
`finrank` *lower bound* `h622lb` needs; `h622lb`'s RHS is exactly the span L7a's brick bounds; the
split realization's seed is alg-indep (the footnote-6 input); `splitOff_removeVertex_minimalKDof`'s
`k' ≤ D−2` is exactly what makes `h622lb`'s bound the weakest of the `−k'` family.

### 1.70 The L8 signature pin — the Lemma-6.5 arm, `h65` *discharged* via KT Claim 6.6 (graph side) + the Π°-placement producer (geometric side): the two-vertex-removal arm of the Case-I dispatch. KT Claim 6.6 FORCES `k = 0` (the hypotheses make `G` a 0-dof-graph), so the producer concludes inside the `k=0` stratum and discharges the `theorem_55_d3:516` 0-dof `h65` directly; the all-`k` `case_I_dispatch:1867` `h65` is discharged by the SAME producer after an internal `k = 0` derivation (its hypotheses force `def(G̃) = 0`). The geometric side IS the L6 Case-II template (Brick A `le_finrank_span_rigidityRows_of_pinned_placement` + the §1.62 deficiency-aware rank-polynomial transfer), with the NEW block being the TWO `v`-edges spanning the full `D` (KT Lemma 5.3, the one genuinely-new geometric sub-leaf) instead of L6's single split-off edge spanning `D−1`. V11 RESOLVED — buildable, NO motive/IH change: Claim 6.6 needs a NEW maximal-proper-rigid-subgraph existence lemma (genuinely-new combinatorics, bounded by `α` finite) and KT-Lemma-4.4 reused in the +`v` direction (the landed `removeVertex_deficiency_ge` is EXACTLY that direction). One privacy fix: de-privatize CaseIII's triple-LI bridge. **Loop-case refinement (c′), 2026-06-15:** the L8a-step-2 build surfaced that the maximal `G'` must be taken INDUCED (`G.induce V(G₀)`) to kill the contraction's loop mode — KT's silent edge-saturation; one more NEW brick `deficiency_le_deficiency_of_le_vertexSet_eq` (def antitone under edge addition at fixed vertex set). No definitional change. **Steps-3–5 pin (c″), 2026-06-15:** the `G''` carrier is `addEdge`-twice (`(G'.addEdge eₐ v a).addEdge e_b v b`, no bespoke def); step 4's minimality→graph-equality is ONE new brick `eq_of_isMinimalKDof_of_le_of_vertexSet_eq_of_isKDof` (a near-clone of the landed `edgeSet_ncard_le_two_of_isMinimalKDof_of_ncard_two` body), buildable, no motive/user decision (2026-06-15). **L8c geometric-core pin (i), 2026-06-15:** the Leaf-2 step-4 `hnewpin` (TWO `v`-edges spanning `D`) RE-RATED from (d)/(h)'s "build-time uncertainty leaf" to a pinned NEW `RigidityMatrix.lean` brick `exists_independent_pinned_two_edge_span_full` (P≈3.5, route via `finrank_sup_add_finrank_inf_eq` + `dualAnnihilator_sup_eq` + `exists_fun_fin_finrank_span_eq` — coordinator-verified consumer-fit against Brick A's verbatim `hnewpin`), and the `case_I_realization_h65` producer's exact Brick-A assembly pinned against Brick A's verbatim signature — template is `case_II_realization_all_k` (NOT `case_I_realization_all_k`, which uses the high-level coupler), OLD-block `hold_span` genuinely simpler (`G_v ≤ G` literal subgraph, one named seed-restriction `funext` flag), producer FORCES `ends eₐ=(v,a)`/`ends e_b=(v,b)` to avoid L6's swap branch. Buildable leaf sequence: L8c-1 `hnewpin` brick → L8c-2 producer + privacy + wiring. See §1.70(i)

**Docs-only design pass (opus, 2026-06-15).** Every load-bearing decl (Theorem55, CaseII, CaseIII,
RigidityMatrix, SplitOffDeficiency, ForestSurgery, Deficiency, ReducibleVertex, Operations, PanelHinge)
opened to its body and checked against KT 2011 §6.2, pp. 676–677 (Lemma 6.5, Claim 6.6, the Π°-placement
map, the (6.10) block-triangular rank chain). No `.lean`/`.tex` edits this pass.

**The slot.** L8 discharges `h65`, the negative arm of the Case-I dispatch's inner `by_cases
(G.rigidContract H r).Simple`: a simple minimal-dof `G` that has a proper rigid subgraph but no
contraction of one is simple. KT routes this to Lemma 6.5, the vertex-removal argument.

**(a) The two carried `h65` shapes RECONCILE to one producer.** `theorem_55_d3:516` carries a
`k=0`-only `h65`; the all-`k` `case_I_dispatch:1867` carries an all-`k` `h65`. Against KT: Claim 6.6's
proof forces `G` itself to be 0-dof whenever the hypotheses hold (the maximal proper rigid subgraph
`G'` is 0-dof, `G'' = G'+v+{e,f}` is 0-dof by Lemma 4.4, maximality+minimality force `G = G''`), so the
all-`k` carry's `k` is always `= 0` in practice — its producer derives `k=0` internally from `hG` +
Claim 6.6, then runs the `k=0` argument. One producer `case_I_realization_h65` discharges both:
`theorem_55_d3` calls it directly now (the nested `G_v` is *also* 0-dof here, unlike L7's Case III, so
the `k=0`-only IH suffices); `case_I_dispatch` calls it after L9's spine wiring. No motive/IH change,
no adjudication.

**(b) Leaf decomposition.** Two leaves + a wiring commit: **Leaf 1** (Claim 6.6's graph side, NEW
combinatorics) → **Leaf 2** (the Π°-placement producer `case_I_realization_h65`, geometric side) →
**wiring** (drop `theorem_55_d3`'s `h65` carry, restate `lem:case-I-dispatch` green).

**(c) Leaf 1 — the Claim 6.6 graph-side lemma.** Pinned conclusion:
`exists_degree_two_removeVertex_of_no_simple_contraction` produces `v,a,b,eₐ,e_b` with `v` degree
exactly 2 (neighbours `a,b`), `G_v := G.removeVertex v` minimal 0-dof and simple. Proof (KT Claim 6.6,
pdf p. 30): **step 1** take a vertex-cardinality-maximal proper rigid subgraph `G'`
(`exists_maximal_isProperRigidSubgraph`); **step 2** non-simplicity of `G/E(G')` gives a vertex
`v∉V(G')` with two edges into `V(G')` (the *parallel* disjunct of `rigidContract_not_simple` — the
fiddliest sub-step, P≈3; **but see (c′): the *loop* disjunct is not vacuous as literally read**);
**steps 3–5** `G'' := G'+v+{eₐ,e_b}` is 0-dof by Lemma 4.4 (`removeVertex_deficiency_ge`,
SplitOffDeficiency.lean:405, exact direction confirmed), maximality+minimality force `V=V'∪{v}` and
`G=G''`, so `v` is the sought degree-2 vertex and `G_v=G'`. Genuinely-new content: step 1's existence +
step 2's extraction; steps 3–5 are landed bricks + bookkeeping.

**(c′) Loop-case fix — take `G'` INDUCED.** `IsProperRigidSubgraph` is a *plain*-subgraph relation, not
induced, so a `G`-edge with both ends in `V(G')` need not lie in `E(G')` — exactly the case
`rigidContract_not_simple`'s *loop* disjunct describes, and a vertex-cardinality-maximal `G'` does not
rule it out (KT's proof silently assumes edge-saturation). Fix: replace `G'` by the induced saturation
`G.induce V(G₀)` of the cardinality-maximal `G₀` — landed as `exists_maximal_induced_isProperRigidSubgraph`
(Deficiency.lean:798), consuming the NEW brick `deficiency_le_deficiency_of_le_vertexSet_eq` (`H≤H'` at
equal vertex sets ⟹ `def(H'̃)≤def(H̃)`, P≈2, a `partitionDef`-monotone-in-crossing-count argument). On
the induced `G'`, `edgeSet_induce` kills the loop disjunct, leaving only the parallel extraction step 2
always intended. No change to `IsRigidSubgraph`'s definition; matches KT's own (silent) edge-saturation
of the maximal subgraph.

**(c″) Steps 3–5 pin.** Carrier `G'' := (G'.addEdge eₐ v a).addEdge e_b v b` (no bespoke `def`; four
facts verified: `V(G'')=V(G')∪{v}`, `v` has degree exactly 2, `G''.removeVertex v = G'` — the one place
`G'`'s induced-saturation is load-bearing again — and `G''≤G`). Step 4's "minimality of `G` ⟹ `G=G''`"
needs a matroid-counting brick (minimality is base-meets-every-fiber, not "no removable edge"), landed
as `eq_of_isMinimalKDof_of_le_of_vertexSet_eq_of_isKDof` — a near-clone of the landed
`edgeSet_ncard_le_two_of_isMinimalKDof_of_ncard_two` (Deficiency.lean:2253). Buildable, no motive/user
decision.

**(d) Leaf 2 — the Π°-placement producer, `case_I_realization_h65`.** Signature matches
`theorem_55_d3:516`'s `h65` carry exactly (same hypotheses, conclusion `HasGenericFullRankRealization
2 n G`). Body (the L6 `case_II_realization_all_k` template widened): Leaf 1 gives `v,a,b,eₐ,e_b`; the
`k=0`-only IH at `G_v` (also 0-dof) gives a realization `Q_v` at rank `D(|V_v|−1)`; extend the seed at
`v` by a fresh Π° normal making `![q(v,·),q(a,·),q(b,·)]` triple-LI (the §1.53 bridge); Brick A
(`le_finrank_span_rigidityRows_of_pinned_placement`) with the NEW block = the two `v`-edge hinge rows
(spanning the full `D`, KT Lemma 5.3) and the OLD block = `Q_v`'s rows (unchanged, same seed — no
rank-polynomial transfer needed, UNLIKE L6/L7) gives rank `≥ D(|V|−1)`; B2 + antisymmetry close it. The
one genuinely-new geometric piece is the NEW block's `D`-element independent-and-spanning claim
(**flagged build-time, see (i)**); the SAME-pair `eq_of_hingeConstraint_two_parallel` does not apply
since the two `v`-edges have *distinct* other endpoints.

**(e) The privacy fix.** `linearIndependent_normals_of_algebraicIndependent` (CaseIII.lean:3407, the
triple-LI bridge Leaf 2 needs) is `private`, and Leaf 2 lives downstream in Theorem55.lean. Resolution:
de-privatize it (a clean, general, reusable fact; its one existing caller is unaffected) rather than
re-mirror or relocate Leaf 2.

**(f) Ordered leaf list.** L8a-0 (the def-antitone brick, (c′)) → L8a step 2 (the shared-`v`
extraction) → L8a (Leaf 1 assembly) → L8b (the privacy fix, rides in L8c) → L8c (Leaf 2 + wiring: drop
`theorem_55_d3`'s `h65` carry, restate `lem:case-I-dispatch` green, statement-grep gate on
`case_I_dispatch`/`theorem_55_d3`). If the full pin doesn't fit one sitting, **L8a alone is a clean
stopping point.**

**(g) Verdict.** Every cited landed fact (`removeVertex_deficiency_ge` = KT Lemma 4.4 exact direction;
Brick A; `case_II_realization_all_k`'s template; the CaseIII triple-LI bridge; `finrank_hingeRowBlock` /
`screwSpace_finrank`) checked against its body. No motive/IH change; no user adjudication — the two
`h65` shapes reconcile internally and the privacy issue resolves to a de-privatization. Genuinely-new:
L8a-0 (P≈2), Leaf 1 step 2's extraction (P≈3), and Leaf 2 step 4's `hnewpin` (P≈3, flagged — resolved
in (i)); Leaf 2's "`G_v` is 0-dof" step rests on Leaf 1's `G−v=G'` but is otherwise insulated from Leaf
1's internal difficulty. Estimate ~3–4 commits; L8 is simpler than L7 (no rank-polynomial transfer) but
carries more new combinatorics (the maximal-subgraph existence + non-simplicity unpacking).

### 1.70(i) The L8c geometric-core pin — the Leaf-2 step-4 `hnewpin` brick (RE-RATED to a pinned NEW brick) + the `case_I_realization_h65` exact Brick-A assembly (DESIGN-SETTLE, 2026-06-15, opus, docs-only)

The (d) build-time-uncertain `hnewpin` step now settles to a pinned NEW brick with an exact route
(every load-bearing decl re-opened to its body this pass, two mathlib tools verified by loogle). Net
verdict (clause ii): no motive/IH change, no user adjudication — one honest flag, the (i.2)
seed-restriction step.

**Finding 0.** The structural template is `case_II_realization_all_k` (CaseII:297, which consumes
Brick A directly at CaseII:1063), NOT `case_I_realization_all_k` (which assembles through the
high-level block-triangular coupler and never touches Brick A) — confirming §1.70(d)'s "the L6
Case-II template widened" reading.

**(i.1) The `hnewpin` brick — PINNED, genuinely new.** Need: a `D`-element independent family through
`v`'s screw column spanning the full `D` (KT Lemma 5.3, the *distinct*-endpoint form — the per-edge
tools each give only `D−1`, and the SAME-pair `eq_of_hingeConstraint_two_parallel` does not apply).
Route (every sub-fact landed/mathlib): `finrank(U⊔W) = finrank U + finrank W − finrank(U⊓W)`
(`Submodule.finrank_sup_add_finrank_inf_eq`); `U⊓W = (span Cₐ ⊔ span C_b)^⊥`
(`Submodule.dualAnnihilator_sup_eq`); `finrank(span Cₐ ⊔ span C_b) = 2` (the two LI supporting
extensors, themselves supplied by the CaseIII triple-LI bridge (e) at `(a,b,c):=(v,a,b)`) gives
`finrank(U⊔W)=D`; extract a `Fin D`-indexed LI subfamily via `Submodule.exists_fun_fin_finrank_span_eq`.
**LANDED** as `BodyHingeFramework.exists_independent_pinned_two_edge_span_full` — in **`Pinning.lean`**,
not `RigidityMatrix.lean` (avoids a circular import: the brick consumes `panelRow`/per-edge tools
downstream of `RigidityMatrix`), and with two added link hypotheses `hlink_a`/`hlink_b` that
`hnew_span`'s `panelRow_mem_rigidityRows` needs (both corrections forced by landed source, no math
change). P≈3.5, buildable, not research-shaped. *(One non-load-bearing aside corrected in-pass: the
reverse `(U⊓V)^⊥=U^⊥⊔V^⊥` direction IS available for field subspaces, `Subspace.dualAnnihilator_inf_eq`
— not needed here, `dualAnnihilator_sup_eq` stays the right tool.)*

**(i.2) The producer's exact Brick-A assembly.** `case_I_realization_h65` instantiates Brick A with
`ιn` = the (i.1) brick's `D`-element NEW index and `ιo` = the IH's `G_v`-row OLD index, mirroring
`case_II_realization_all_k`'s CaseII:1036–1069 template. The producer *forces* `ends eₐ=(v,a)`,
`ends e_b=(v,b)` by construction, avoiding L6's swap-branch gymnastics entirely. The one honestly-new
step beyond assembly: `hold_span` (the OLD block lies in `span Q.rigidityRows`) needs the
*seed-restriction* fact "`Q`'s normals on `V(G_v)` = `Q_v`'s normals" stated explicitly (mechanically
true — the extended seed agrees with `Q_v`'s off `v`, and `G_v`-vertices are `≠v` — but a real proof
obligation, `funext` + `Function.update_of_ne`, P≈2). This is the genuinely-*simpler*-than-L6 step:
`G_v≤G` is a real subgraph (unlike L6's `splitOff`), so `hold_span` is the §1.68(d) TRIVIAL case, not a
70-line extensor-agreement argument.

**(i.3) Buildable leaf sequence.** L8c-1 (the (i.1) brick, **LANDED**) → L8c-2 (the producer + L8b
privacy fix + wiring: rewrite `theorem_55_d3`'s `:555` lambda, drop the `h65` carry, restate
`lem:case-I-dispatch` green — statement-grep gate on `theorem_55_d3`).

### 1.71 The L10 signature pin — Theorem 5.6 at `d = 3` (the `def > 0` `prop:rigidity-matrix-prop11` feed): **V9 RESOLVED FREE** (the homogeneous projective move is already landed as `exists_extensor_in_two_panels`), the deficiency-preserving spanning-strip is a NEW greedy edge-deletion brick (verified absent in tree), the `def > 0` `hgen` feed assembles strip → `theorem_55_all_k` (after `subgraph_minimality`) → `withGraph` re-add (`finrank_infinitesimalMotions_le_of_graph_le`, landed) → `rigidityMatrix_prop11`; sliced L10a–L10d (2026-06-16, opus, docs-only)

**Landed 2026-06-16 (Phase 22k CLOSED).** All flags below resolved favorably, no motive/IH/`def` change
anywhere; KT Thm 5.5 + Thm 5.6 formalized at `d = 3` — full build-time detail in `notes/Phase22k.md`.

**(a) V9 — the homogeneous projective re-add is FREE.** KT's Thm 5.6 re-add (p. 670) splits into two
purposes: the rank *lower bound* (KT: "obvious") is the already-green `lem:motions-mono-of-graph-le` =
`finrank_infinitesimalMotions_le_of_graph_le` — unconditional on the re-added edges' genericity, since
`withGraph` keeps the same `supportExtensor` and `infinitesimalMotions` only quantifies over links. The
*valid-realization* half (KT's actual use of projective invariance, needing each re-added edge's two
panels to meet) is free in the project's homogeneous model: two linear hyperplanes through the origin in
`ℝ^{d+1}` always meet in dimension `≥ d − 1`, no transversality hypothesis needed, and the producing
brick `exists_extensor_in_two_panels` (`PanelLayer.lean:631`, built for the L4a cut-edge case) already
supplies it. No genuinely-new geometry.

**(b) The spanning-strip brick — NEW, verified absent in tree.**
`Graph.exists_isMinimalKDof_spanning_subgraph` (`G' ≤ G`, `V(G') = V(G)`, `G'.IsMinimalKDof n
(G.deficiency n)`), designed via greedy edge deletion under matroid-rank descent
(`rank_add_deficiency_eq` at fixed `V`, a WF recursion on `|E(G)|`). FLAG (buildable, not a blocker):
"no-deletable-edge ⟺ `IsMinimalKDof`" was stated in the docstring but not yet a landed lemma — a P≈3.5
matroid leaf (contrapositive of `subgraph_minimality`'s engine), not a one-liner. **Landed via a cleaner
route than designed:** a finite minimum (`Set.exists_min_image` over deficiency-preserving edge subsets),
not the WF recursion above — the flag dissolved outright, no separate micro-pin needed.

**(c) The `def > 0` `hgen` feed — end-to-end assembly.** Producer
`PanelHingeFramework.rankHypothesis_of_theorem_55_d3`. **Route (matches the landed build):** strip (b) →
`theorem_55_minimalKDof_k` (realize the spanning subgraph at its own deficiency) → `withGraph`/`reaimSub`
re-add → `hgen` from `finrank_infinitesimalMotions_le_of_graph_le` monotonicity → `rigidityMatrix_prop11`
— realize-then-re-add, NOT the Brick-A span-transport placement route (§1.68). **Load-bearing FLAG,
surfaced not forced:** the design pass found `theorem_55_all_k` as landed concludes only at a *0-dof*
minimal graph (`hG : G.IsMinimalKDof n 0`); the (b) strip lands a `k`-dof `G'` with `k = def(G̃) > 0`, so
the spine needed a general-`k` re-expose whose cost (a one-line wrapper vs. a producer silently assuming
`k = 0`) could not be settled from the design pass alone. **Resolved free at build time:**
`theorem_55_minimalKDof_k` landed as the near-free wrapper (identical callback map, only the final
`0 G hG` argument generalized to `k G hG`) — no producer assumed `k = 0`.

**(d) Sub-layer plan + blueprint flip.** Ordered leaves: L10a (the (b) strip, P≈3.5) → L10b (the (c)
all-`k` re-expose, P≈1 if free) → L10c (the (c) producer, P≈3, one `reaim`-style micro-brick for the
re-added edges' in-two-panels extensor) → L10d (blueprint: green `prop:rigidity-matrix-prop11`, mint
`thm:theorem-55-6-d3` `\uses{thm:theorem-55-d3-instance, lem:motions-mono-of-graph-le,
lem:subgraph-minimality, prop:rigidity-matrix-prop11}`; `thm:theorem-55` stays red, general `d`, Phase
23). Estimate ≈3–4 commits if both flags resolve favorably, more if the (c) flag is a real gap —
flagged, not forced. **Build-time correction:** the plan above also re-routes
`prop:rigidity-matrix-prop11`'s own proof to `\uses` the new `thm:theorem-55-6-d3` node — together with
the new node's own `\uses{…, prop:rigidity-matrix-prop11}`, a literal *mutual* `\uses` cycle that blows
plastex's `ancestors` recursion. Landed one-way instead: only `thm:theorem-55-6-d3`'s proof `\uses` the
prop; the prop's own proof re-routes onto `thm:theorem-55` + `lem:motions-mono-of-graph-le` (dropping the
reverse edge), keeping the dep-graph acyclic.
