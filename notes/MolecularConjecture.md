# Molecular Conjecture — cross-phase program plan

**Status:** IN PROGRESS. Phases 17–22f + 21a complete; the current frontier is the
**deferred, unlettered `d=3` realization assembly** (`prop:rigidity-matrix-prop11` `hub` +
`thm:theorem-55` flip + wiring `case_I_realization` into the Case-I branch — what finally
takes the two producer nodes `lem:case-II-realization` / `lem:case-III` green), then
**Phase 23** (general `d`). **Phase 22f** (✓ complete, closed 2026-06-07) landed N3b — the
point-join↔panel-meet duality `pᵢ∨pⱼ = λ·C(L)` (bounded `⋀²ℝ⁴` exterior-algebra,
`complementIso_smul_eq_extensor_join` / `extensor_join_eq_zero_of_complementIso_eq_zero`) —
discharging 22e's last red leaf, so KT Claim 6.12 and the candidate-completion chain are now
fully green. **Phase 22e** (✓ complete, closed 2026-06-07) delivered the candidate-completion +
KT Claim 6.12 for Case III at `d=3` (KT §6.4.1): the missing `+1` row construction and the
three-candidate disjunction, the successor to 22d
(whose crux KT Claim 6.11 / eq. (6.23), the redundant `ab`-row, landed green +
axiom-clean at the close of Phase 22d). Phases
17–20 + 21a delivered `M(G̃)`, deficiency, `k`-dof, the def = corank bridge, the
Theorem-4.9 combinatorial induction, and the Grassmann–Cayley meet (see
`notes/Phase19.md`, `notes/Phase20.md`, `notes/Phase21a.md`). Phase 21
(algebraic induction) is **complete, GREEN-modulo-21b**: all
genericity-free content green (panel layer, Theorem 5.5, Cases I/II, the
analytic half of Prop 1.1), with the shared analytic crux Claim 6.4/6.9
(the genericity device) scoped out into its own sub-phase **Phase 21b**,
entering each consuming node as an explicit hypothesis (risk #4/#7 +
`DESIGN.md` *Genericity device (Claim 6.4/6.9) is its own sub-phase
(Phase 21b)*). **Phase 21b is complete** (closed 2026-06-04): it delivered
the genericity device, the genericity-free accounting iffs, and the
`V(G)`-relative count bridges. A math-first feasibility pass against KT
§6.2–6.3 then **re-scoped the realization *producers* to Phases 22–23** and
corrected the case-naming — **the project's reducible-vertex split
(`theorem_55`'s `hsplit`, k=0) is KT Case III, not Case II** (it is one row
short of full rank via eq. (6.12) and needs the Lemma 6.10/6.13 redundant-edge
row); only the rigid-subgraph contraction (Case I) reaches full rank. The KT
math for both producers is worked out in `notes/Phase21b.md` *Finding A/B* +
*Hand-off to Phases 22–23* and folded into the *Phase 22+* plan below.
**Phase 22 (the realization layer) is sub-lettered.** Opened as a single Phase 22
on 2026-06-04, it was split the same day because it over-broadly bundled three
independent bodies of work; sub-lettering (22a, 22b, …) keeps the integer phase
numbers 23–26 stable. **Phase 22a is complete** (Case I
realization, KT §6.2; see `notes/Phase22a.md`): the composer
`PanelHingeFramework.case_I_realization` (`lem:case-I-realization`) discharges
`theorem_55`'s Case-I branch, delivered via the **block-triangular
reframe**: KT eq. (6.3)'s rank-addition over one common framework
`ofNormals G ends q₀`, routed through the genericity device's independent-row count
(the H-block edges ⊔ the surviving edges made independent by the exterior-column
projection), not a common-seed splice. It shipped green-modulo a single dischargeable
hypothesis = KT **Claim 6.4** (`lem:claim-6-4`, the surviving block's exterior-projected
rank at the generic placement, KT eqs. (6.5)/(6.9)), **fully discharged in Phase 22b**
(so `lem:case-I-realization` is now fully green). The phase's cross-cutting lesson — a formalization must reproduce
the source's argument **structure**, not just its conclusion — surfaced from the
hpinc→asymmetric→block-triangular→Qc-non-root design arc (the common-seed splice
type-checked but kept needing undischargeable bridge hypotheses) and is promoted to
`DESIGN.md` *Match the source's argument structure, not just its conclusion*. The
full Case-I brick inventory (N4 contraction-minimality bridge via the Whitney-style
sub-build N4a→N4b→N4c, the N5 splice/seed/rank-polynomial bricks, N6a/N6b/N6c, the
two-motive split, the generic-motive induction G2a–c / G3a–c) + decision history
live in `notes/Phase22a.md`. **Phase 22b is complete** (closed 2026-06-05): KT Claim 6.4 — the discharge of 22a's
green-modulo obligation — is **fully discharged** (`lem:claim-6-4` green), so
`lem:case-I-realization` is fully green. The reduction N-22b-1/2/3 cut Claim 6.4 to the single
hypothesis `htransport`; the discharge then built the three composing bricks (U3a the relabel-leg
rigidity transport; **U3b** the genuine crux — the exterior-column projection loses zero rank on a
rigid block, via `Z ⊔ range(extProj) = ⊤` whose one real-content input is the rigid-block pin-count;
U2/U1 the collapse-relabel projected-row reproduction at KT eq. (6.7)'s degenerate placement) and the
route-(i) motive strengthening (the link-recording conjunct, discharging the selector alignment),
composed by the capstone U4 producer `rigidContract_exterior_rank_transport_htransport`. The
course-correction discipline (the crux moved U2→U3, then U3a was found not a leaf) + design arc
(`notes/Phase22-realization-design.md` §1.14–§1.24) are in `notes/Phase22b.md`.
**Phase 22c is stratum-1 complete** (opened 2026-06-05 design-pass-first; stratum-1
producer landed 2026-06-05; crux split out to 22d): Case III at `d=3` (KT §6.4.1, Lemma
6.10) — the `theorem_55.hsplit` producer at `k=0`, the conjecture's crux. **Case III at
`d=3` is multi-phase**; 22c claimed only the FIRST of three difficulty strata: stratum
1, the eq. (6.12) `+(D−1)` block-triangular placement — green + axiom-clean as
`PanelHingeFramework.case_II_placement_eq612` (`rank R(G,p₁) ≥ D(|V|−1)−1`, from the
green Phase-21b N7b row infra). Opened on a **layer-level design recon, not a build**
(Case I burned ~10 node-by-node commits before a layer pass surfaced the binding gap;
`DESIGN.md` *Scale-up: design the LAYER, not just the node*).
**Phase 22d is complete** (opened 2026-06-05 design-pass-first, re-scoped 2026-06-05 per a
fresh user direction, closed at the Claim 6.11 milestone): it attacked the conjecture's
hardest node — KT **Claim 6.11**, the *missing `+1` row* lifting 22c's `D(|V|−1)−1` brick
toward full `D(|V|−1)` — **bottom-up**, building the prerequisite chain green + axiom-clean
rather than axiomatizing the claim (user override of the opening axiomatize-as-hypothesis
verdict). The discharge factored through three combinatorial↔linear gaps (matroid-base
4.3(ii) → nested IH-at-restriction → the `M(G̃)`↔row bridge), all green, on a seed-rank
analytic kernel that forced the project's first algebraic-independence use. The
candidate-completion + Claim-6.12 disjunction and the `d=3` assembly are the deferred,
UNLETTERED successor. See the *Phase 22d* detail block below + ROADMAP §22d.
Phases 23–26 planned. This is the program design for Phases 17–26 and the runbook for
threading the remaining phases.
**Audience:** the agent picking up the molecular-conjecture program.
Read this after `ROADMAP.md` (which carries the one-paragraph program
summary + status row); this file is the lemma-level detail.

When opening or closing each remaining phase, follow the top-level
`CLAUDE.md` *When this commit opens / closes a phase* protocol — and
**keep this doc current as part of it** (its phase table, the per-phase
detail block, and *Opening the next phase*). This cross-phase program doc
is gated by no CI/checkdecls check, so it drifts unless synced at every
molecular phase boundary (it did, pre-21b). Per-phase blueprint nodes go
in that phase's chapter (`extensor.tex` / `rigidity-matrix.tex` / …, or by
extending `algebraic-induction.tex` for the 21/22+ realization layer), not
a single `molecular.tex`.

The *detailed-exposition* deliverable for this program (spelling out the steps
KT's paper compresses, so each crux is followable end-to-end) is tracked in
`notes/BlueprintExposition.md` — the cross-phase ledger of hard nodes that earn
a full followable blueprint proof (most of its entries are
molecular: Lemma 2.1, Prop 1.1's two halves, the Thm-4.9 forest-surgery
track, the Case I/II/III cruxes). **Capture** a one-line entry there when a
node reroutes and surfaces a stable KT-math insight; **write** the prose at
that phase's close. Keep it current at each molecular boundary alongside this
doc (it is likewise gated by no CI check).

## The target

The **Molecular Conjecture** (Tay–Whiteley 1984, proved by
Katoh–Tanigawa 2011): a graph `G` can be realized as an
infinitesimally rigid **body-hinge** framework in `ℝᵈ` iff it can be
realized as an infinitesimally rigid **panel-hinge** framework in
`ℝᵈ`. Combined with the Tay–Whiteley body-hinge theorem (our Phase 16,
KT Proposition 1.1), this says: `G` has a rigid panel-hinge realization
iff `(D−1)·G` contains `D` edge-disjoint spanning trees, where
`D = (d+1 choose 2)`.

The hard content is that forcing the hinges at each body to be
**coplanar** (panel-hinge) does not drop the rank below the generic
body-hinge value. KT prove the strong quantitative form:

- **Theorem 5.5** (the heart): every *minimal `k`-dof-graph* `G` with
  `|V| ≥ 2` has a (nonparallel, if `G` simple) panel-hinge realization
  with `rank R(G,p) = D(|V|−1) − k`.
- **Theorem 5.6**: every multigraph `G` has a panel-hinge realization
  with `rank R(G,p) = D(|V|−1) − def(G̃)` — the conjecture, strong form.
- **Corollary 5.7** (the *molecule application*, requested in scope):
  for `G` with min degree ≥ 2, the rank of the 3-D generic bar-joint
  rigidity matroid of the square satisfies `r(G²) = 3|V| − 6 − def(G̃)`.

User-chosen scope (2026-06-02): **full conjecture + molecule
application**, with the molecule app **fully formalized** (not
citation-stubbed), built on a **full Grassmann–Cayley extensor
algebra** layer.

## Source and verified citations

Primary source: **Katoh, N., Tanigawa, S.**, *A Proof of the Molecular
Conjecture*, Discrete Comput. Geom. **45** (2011), 647–700
(`.refs/katoh-tanigawa-2011-molecular-conjecture.pdf`; the 2009 arXiv
version is also under `.refs/`). All section/lemma/theorem numbers
below were read directly from that PDF.

**Numbering convention.** Bracketed `[N]` throughout this file are
Katoh–Tanigawa 2011's own reference-list numbers (their bibliography,
pp. 699–700) — kept so entries line up with the paper, not a local
list. The full citations of every `[N]` used appear either inline below
or in the *Reference availability* note that follows.

External results KT *cite rather than prove*; we mirror that boundary
(formalize or axiomatize as noted per phase). Verified against KT's
bibliography (page 699–700):

- **[4] Crapo, H., Whiteley, W.**, *Statics of frameworks and motions
  of panel structures: a projective geometric introduction*, Structural
  Topology **6** (1982), 43–82. — projective invariance of
  infinitesimal rigidity (§1.2, §5.2, §6); cycle realization Lemma 5.4.
- **[29] White, N., Whiteley, W.**, *The algebraic geometry of motions
  of bar-and-body frameworks*, SIAM J. Algebraic Discrete Methods
  **8** (1987), 1–32. — the "pinning a body preserves the motion
  space" fact behind Lemma 5.1.
- **[15] Jackson, B., Jordán, T.**, *The generic rank of
  body-bar-and-hinge frameworks*, European J. Combin. **31** (2009),
  574–588. — the generic-rank ↔ matroid-deficiency bridge
  (Theorem 6.1: `r(G,q) = D(|V|−1) − def_D(G_H)`; Corollary 6.2: rigid
  iff `G_H` has `D` edge-disjoint spanning trees; `def_k` defined in §4
  after Theorem 4.1); also the generic-max-rank property of §6.
- **[2] Barnabei, M., Brini, A., Rota, G.-C.**, *On the exterior
  calculus of invariant theory*, J. Algebra **96** (1985), 120–160.
  — Grassmann–Cayley foundations (extensors / join).
- **[13] Jackson, B., Jordán, T.**, *On the rigidity of molecular
  graphs*, Combinatorica **28** (2008), 645–658. — the published
  primary source for the molecule-graph rigidity rank (Cor 5.7).
  Whiteley's *equivalence of molecular rigidity models* (KT [35]) is
  only an unpublished 2004 preprint, so [13] is the citable anchor.
- **[37] Whiteley, W.**, *Counting out to the flexibility of
  molecules*, Physical Biology **2** (2005), S116–S126
  (`.refs/whiteley-2005-counting-flexibility-molecules.pdf`). — survey
  presentation of the molecule ↔ body-hinge modelling.
- Tutte 1961 [26] / Nash-Williams 1961 [20] (Proposition 2.2) and
  Oxley [21] (count-matroid corollary) — already in the project
  (Phases 12–13); reused, not re-cited as new.

**Reference availability in `.refs/` (checked + completed 2026-06-02).**
All load-bearing and medium-priority sources are now present and text-
extractable: KT 2011 (+2009 arXiv), Nash-Williams 1961, Tutte 1961,
Oxley (2011 2nd ed), Schrijver, Tay 1989, Whiteley 1988/1996/2005,
Jackson–Jordán 2006 pin-collinear, **[4] Crapo–Whiteley 1982** (proj.
invariance, Phase 25; cycle Lemma 5.4, Phase 21), **[13] Jackson–Jordán
2008** *On the rigidity of molecular graphs* (Cor 5.7, Phase 26),
**[15] Jackson–Jordán 2009** (Thm 6.1 / Cor 6.2 rank-deficiency bridge), **[29] White–Whiteley
1987** (pin-a-body, Lemma 5.1, Phase 18), **[34] Whiteley 1999** Kluwer
(Lemma 5.4). The Phase-17 Grassmann–Cayley foundations are also all in
place (text-extractable, added 2026-06-02): **[2] Barnabei, M., Brini,
A., Rota, G.-C.**, *On the exterior calculus of invariant theory*, J.
Algebra **96** (1985), 120–160; **[6] Doubilet, P., Rota, G.-C., Stein,
J.**, *On the foundations of combinatorial theory IX: Combinatorial
methods in invariant theory*, Studies in Applied Mathematics **53**
(1974), 185–216; **[28] White, N. L.**, *Grassmann–Cayley algebra and
robotics*, J. Intelligent & Robotic Systems **11** (1994), 91–107
(DOI 10.1007/BF01258296). (These three are background for Lemma 2.1's
extensor conventions, not strictly required — Lemma 2.1 is
self-contained from KT + mathlib `ExteriorAlgebra`.)

**The reference set is complete** — every source the program needs
(load-bearing, medium, and optional) is present in `.refs/` and
text-extractable. Nothing outstanding to acquire.

**OCR note.** [4] Crapo–Whiteley and `tay-whiteley-1985-generating-
isostatic` arrived as image-only scans (no text layer) and were OCR'd
in place on 2026-06-02 (`pymupdf` render at 300 dpi → `tesseract` 5.5.2
searchable PDF, replacing the scan losslessly). Both are *Structural
Topology* / *Topologie Structurale* journal articles with **side-by-
side English|French columns**; tesseract auto-detected the columns and
kept each contiguous (no interleaving), but only the `eng` language
pack is installed, so per page the text extracts as the full (eng-OCR'd,
imperfect) French column followed by the clean English column. Read the
English run; math symbols are imperfect (scan OCR) but the prose proof
structure is intact. To read a page via `pypdf`, expect French-then-
English ordering. Note: `.refs/` is gitignored, so these OCR'd PDFs are
local-only and not committed.

**Citation accuracy caveat (per `CLAUDE.md` *Referencing prior work*).**
Lemma 5.4 (cycle realizations) is cited by KT to [4] and [34]
(Whiteley, *Rigidity of molecular structures*, Kluwer 1999); verify the
exact proposition numbers in those sources before pinning a `§N` in the
blueprint. Cor 5.7's rank formula is Jackson–Jordán [13]'s result;
attribute it to them, with KT as the conjecture-resolving input.

## Proof architecture — five strata

In dependency order. The phase cuts follow these strata.

1. **Grassmann–Cayley / extensor algebra** (§2.1). Genuinely new linear
   algebra. Load-bearing fact: **Lemma 2.1** — the `D = (d+1 choose 2)`
   many `(d−1)`-extensors of `d+1` affinely independent points are
   linearly independent. Everything in Case III bottoms out here.
2. **The genuine panel-hinge rigidity matrix `R(G,p)`** (§2.2–2.4).
   Honest geometry: `(d−2)`-affine-subspace hinges, the orthogonal-
   complement block `r(p(e))`, screw-center columns, `Z(G,p)`, trivial
   motions, the `rank ≤ D(|V|−1)` bound, degree of freedom, generic
   realizations. **Supersedes Phase 16's reduction-only
   `BodyHingeFramework`** and must be reconciled with it. Carries the
   three foundational rank lemmas 5.1/5.2/5.3.
3. **The matroid `M(G̃)` and `k`-dof combinatorics** (§2.5, §3).
   `D`-deficiency, `k`-dof / minimal `k`-dof-graphs, rigid subgraphs.
   `M(G̃)` is the `(D,D)` count matroid at the **boundary regime
   `ℓ = D = 2k`** — i.e. the `D`-fold graphic-matroid union + Tutte–
   Nash-Williams of **Phases 13–14**, NOT the `ℓ<2k` `CountMatroid.lean`.
4. **The combinatorial induction** (§4). Splitting-off / edge-splitting
   / rigid-subgraph contraction as graph operations; forest-surgery
   Lemmas 4.1/4.2 (hardest new pure combinatorics); the three-case
   decomposition; **Theorem 4.9**.
5. **The algebraic induction** (§5–6). Theorem 5.5 by induction on
   `|V|`: base + Case I (proper rigid subgraph, §6.2) + Case II (`k>0`
   splitting = Whiteley 1-extension, §6.3) + **Case III** (`k=0`, §6.4,
   the `D`-candidate-frameworks argument — "the most difficult case").
   Then Thm 5.6 → Conjecture 1.2, and (strata 6–7 below) the molecule
   application.

The **molecule application** (Cor 5.7) adds, on top:
6. **The 3-D generic bar-joint rigidity matroid** (linear-matroid form).
   Reuses the dimension-general `Framework V d` (Phase 4) + the
   `Matroid.ofFun` linear-matroid framing (Phase 8), specialized to
   `d = 3`. **NOT** a combinatorial (Laman-3D) characterization —
   KT §7 explicitly states that is an *open problem*. We only need the
   linear matroid and its rank `r(·)`.
7. **Projective duality + the molecule modelling equivalence**
   (Crapo–Whiteley [4]; Whiteley/Jackson–Jordán [13,37]): bar-joint of
   `G²` ↔ hinge-concurrent body-hinge of `G` ↔ (projective dual)
   panel-hinge of `G`. Then Cor 5.7 falls out of Thm 5.6.

## Phase breakdown (17–26)

| Phase | Content | KT § | Stratum |
|---|---|---|---|
| 17 ✓ | Grassmann–Cayley extensor algebra; **Lemma 2.1** | §2.1 | 1 |
| 18 ✓ | Genuine panel-hinge rigidity matrix `R(G,p)`; Lemmas 5.1–5.3 (Prop 1.1 deferred to 19) | §2.2–2.4, parts of §5 | 2 |
| 19 ✓ | `M(G̃)`, `D`-deficiency, `k`-dof / minimal `k`-dof, rigid subgraphs, def=corank (JJ Thm 6.1 / Cor 6.2); Lem 3.1/3.3/3.4 | §2.5, §3 | 3 |
| 20 ✓ | Combinatorial induction: graph ops + forest surgery 4.1/4.2 + 4.3–4.8 + **Theorem 4.9** | §4 | 4 |
| 21a ✓ | **GC meet / projective-duality foundations** (the dual half of §2.1): `topEquiv`, `pairingDual`-iso, `complementIso`, `meet` — the substrate the panel layer + Lemma 5.4 + Phase 25 rest on | §2.1 (dual half) | 1 |
| 21 ✓ | Theorem 5.5 skeleton + base + **Case I** (6.2: 6.2/6.3/6.5) + **Case II** (6.3: 6.7/6.8), closing on the **genericity-free** content; **+ panel layer** (coplanar realizations). Genericity (Claim 6.4/6.9) enters as a cited black-box. | §5, §6.1–6.3 | 5 |
| 21b ✓ | **Genericity device** (Claim 6.4/6.9) + genericity-free accounting iffs + `V(G)`-relative count bridges. The realization *producers* re-scoped to 22–23 (math-first pass: the k=0 split is KT Case III, one row short via eq. 6.12; Case I splice is full-rank). | §6.1 (Claim 6.4), §6.3 (Claim 6.9) | 5 |
| 22a ✓ | **Case I realization** (§6.2 splice: full-rank, N4 contraction bridge + N6 composer). `lem:case-I-realization` green-modulo KT Claim 6.4 (`lem:claim-6-4`), via the **block-triangular reframe** (KT eq. 6.3 rank-addition over one common framework, routed through the device's independent-row count). | §6.2 | 5 |
| 22b ✓ | **KT Claim 6.4** (discharge the Case-I green-modulo obligation; closed 2026-06-05, `notes/Phase22b.md`). `lem:claim-6-4` (`case_I_realization`'s former `hclaim64`) is **fully discharged** (`\leanok`), so `lem:case-I-realization` is fully green. The reduction N-22b-1/2/3 cut Claim 6.4 to the single hypothesis `htransport`; the discharge then built the three composing bricks — **U3a** `hasGenericRealization_transport_relabel` (the contraction's generic IH transported to the relabel selector), **U3b** the genuine crux (the exterior-column projection loses zero rank on a rigid block, via `Z ⊔ range(extProj) = ⊤` whose one real-content input is the pin-count `finrank(pinnedMotionsOn t) = D(|Vᶜ|+1−|t|)`, plus the projected-subfamily extraction), **U2/U1** the collapse-relabel projected-row reproduction at KT eq. (6.7)'s degenerate placement — and the **route-(i)** motive strengthening (the link-recording conjunct discharging the U3a alignment + the `H`-leg `hswap`/`hne_ends`). The capstone **U4** producer `rigidContract_exterior_rank_transport_htransport` composes U3a ⊕ U3b ⊕ U2 to supply `htransport` from the contraction's generic IH, wired into `case_I_realization` (deleting its `hbundle`). All axiom-clean. The course-correction arc (the crux moved U2→U3, then U3a was found not a leaf; design doc §1.14–§1.24) is in `notes/Phase22b.md`. | §6.1 (Claim 6.4), §6.2, §5.1 | 5 |
| 22c ✓ stratum 1 | **Case III at `d=3`, stratum 1** (KT Lemma 6.10, the eq. (6.12) `+(D−1)` placement; opened 2026-06-05 design-pass-first, stratum-1 producer landed 2026-06-05, crux split out to 22d, `notes/Phase22c.md`). The conjecture's crux: `theorem_55.hsplit` at `k=0`. **Multi-phase**; 22c claimed only stratum 1 — the eq. (6.12) degenerate placement giving `+(D−1)` (`rank ≥ D(\|V\|−1)−1`, green + axiom-clean as `case_II_placement_eq612`, from the green N7b infra). Nodes `lem:case-II-realization`, `lem:case-III` stay red. Opened on a **layer-level design recon, not a build** (`DESIGN.md` *Scale-up: design the LAYER*). | §6.4.1 | 5 |
| 22d ✓ | **KT Claim 6.11** (the redundant `ab`-row, eq. (6.23)) + its green-machinery prerequisites (closed at the Claim 6.11 milestone; `notes/Phase22d.md`). Attacked the conjecture's hardest node — the *missing `+1` row* lifting 22c's `D(\|V\|−1)−1` brick toward full `D(\|V\|−1)` — **bottom-up**, building the prerequisite chain green + axiom-clean rather than axiomatizing the claim (user override of the opening axiomatize-as-hypothesis verdict). Delivered: the matroid-base 4.3(ii) form at `k=0` (`lem:case-III-claim-6-11-base`, Gap 2), the nested-IH shell `G−v` minimal `k'`-dof with `k' ≤ D−2` (`lem:case-III-gap3-minimalKDof`, Gap 3), the analytic seed-rank kernel (`lem:case-III-seed-rank-bridge` rigidity transfer + `lem:case-III-seed-rank-upper` + `lem:case-III-rank-attainment`), the full `hub` codimension bound (discharged on both consumers), and the redundant-row pigeonhole + row-set identity feeding the eq.-(6.18)/(6.22)⟹(6.23) discharge (`lem:case-III-claim-6-11-redundant-row` → **`lem:case-III-claim-6-11`**, green). The kernel forced the **project's first algebraic-independence use** (KT footnote 6: "*this* seed attains the rank", not "*∃* a seed"); tracker `notes/AlgebraicIndependence.md`. The candidate-completion + **Claim 6.12** disjunction (de-risked on green Lemma 2.1, eq. (6.44) "same `r`") and the `d=3` assembly are the deferred, unlettered successor; its first leaf (eq. (6.28) column-support) landed early under 22d's tail. Nodes `lem:case-II-realization`, `lem:case-III` stay red. | §6.4.1 | 5 |
| 22e ✓ | **candidate-completion + KT Claim 6.12** (Case III at `d=3`, Lemma 6.10; closed 2026-06-07, `notes/Phase22e.md`). Lifts 22c's stratum-1 `D(\|V\|−1)−1` brick to full `D(\|V\|−1)` by converting 22d's green redundant `ab`-row (eq. (6.23)) into the missing `+1` row — the eqs. (6.24)→(6.29) row-op construction of the `v`-column `w` (its eq. (6.28) column-support core already green, landed under 22d's tail = 22e's first leaf) — then the **Claim 6.12** `D`-candidate disjunction (de-risked on the green Lemma 2.1, eq. (6.44) "same `r`"; N3a takes the existence/Zariski route, **not** alg-independence). Closed green-modulo a single N3b duality leaf at the time; that leaf landed in 22f, so the candidate-completion chain (`lem:case-III-candidate-row`) and Claim 6.12 are now fully green. The two target producer nodes `lem:case-II-realization` / `lem:case-III` **stay red** (N10 honest-scope correction: they carry no `\lean`, and their discharge needs the *deferred `d=3` realization assembly*). Opened on a red-node consistency recon (supersession gate clean), not a build. | §6.4.1 | 5 |
| 22f ✓ | **N3b: the point-join↔panel-meet duality bridge** (`lem:case-III-claim612-line-in-panel-union`, completing Claim 6.12 / Lemma 6.10 at `d=3`; closed 2026-06-07, `notes/Phase22f.md`). `pᵢ∨pⱼ = λ·C(L)` for a line `L ⊂ Π(u)`: both the point-join and the panel-meet `C(L) = complementIso(n_u∧n')` lie in the **1-dim** dual-annihilator line `Ω = (dualAnnihilator Φ̃).comap b.toDualEquiv` (`Φ̃ = n_u∧ℝ⁴ + n'∧ℝ⁴`, `dim 5`), the point-join by a Gram-determinant orthogonality, the panel-meet by the green dictionary half — concrete at `⋀²ℝ⁴`, **not** general Hodge theory (`complementIso_smul_eq_extensor_join` + the `r(C)=0 ⟹ r(join)=0` transfer). Discharged 22e's green-modulo-N3b, taking Claim 6.12 (N9) and the candidate-completion chain fully green; the two producer nodes await only the deferred `d=3` realization assembly. | §6.4.1 | 5 |
| ⋯ (deferred, unlettered) | **The `d=3` assembly** (the further cut after 22e/22f — it gets a letter when its turn comes): `prop:rigidity-matrix-prop11` `hub` brick (Track-independent, Phase-19-partition) + `thm:theorem-55` flip + wiring the fully-green `case_I_realization` into `theorem_55_generic`'s Case-I branch. | §5.1, §6.4.1 | 5 |
| 23 | **Case III, general `d`** (Lemma 6.13) → Thm 5.5 complete (incl. `prop:rigidity-matrix-prop11` + `hub`) → **Thm 5.6 → Conjecture 1.2** | §6.4.2, §5.2, §7 | 5 |
| 24 | 3-D generic bar-joint rigidity matroid (linear-matroid form; dim-3 specialization of Phase 4/8) | (J–J [13], Phase 4/8 reuse) | 6 |
| 25 | Crapo–Whiteley projective invariance + molecule ↔ hinge-concurrent body-hinge ↔ panel-hinge equivalence | §1.2 ([4,13,37]) | 7 |
| 26 | **Corollary 5.7**: `r(G²) = 3|V| − 6 − def(G̃)`; the protein-flexibility capstone | §5.2, §1.2 | 6+7 |

**This is a floor of 12 phases** (10 originally; +1 for the Phase-21a
meet foundations inserted by the 2026-06-03 panel re-scope, risk #7;
+1 for the Phase-21b genericity-device sub-phase scoped out of Phase 21
the same day, risk #4/#7). Phases 18, 21, and 22/23 each carry
enough that one or two may split once inside them (precedent: Phases
8–11 spawned perf/cleanup rounds and structural-edit sub-phases). The
program is the largest single undertaking in the project to date —
comparable in effort to Phases 1–16 combined. Sequence the cut-points
as living estimates; re-cut on contact.

### Per-phase detail

#### Phase 17 — Grassmann–Cayley extensor algebra (§2.1) — ✓ Complete

Formalized the Grassmann–Cayley / extensor layer in `Molecular/Extensor.lean`,
landing the hard core **Lemma 2.1** (`omitTwoExtensor_linearIndependent` —
independence of the `D` `(d−1)`-extensors of `d+1` affinely independent points),
on which Case III bottoms out. Detail: ROADMAP §17 + notes/Phase17.md.

#### Phase 18 — Panel-hinge rigidity matrix `R(G,p)` (§2.2–2.4) — ✓ Complete

Built the genuine basis-free panel-hinge rigidity matrix `R(G,p)` in
`Molecular/RigidityMatrix.lean` (with `Z(G,p) = infinitesimalMotions`, the
`rank R ≤ D(|V|−1)` codimension bound) and the three rank lemmas 5.1/5.2/5.3
(`finrank_pinnedMotions_add_screwDim`, `finrank_infinitesimalMotions_le_of_span_le`,
`eq_of_hingeConstraint_two_parallel`). KT Prop 1.1's analytic half relocated
forward to Phase 21+. Detail: ROADMAP §18 + notes/Phase18.md.

#### Phase 19 — `M(G̃)`, deficiency, `k`-dof graphs (§2.5, §3) — ✓ Complete

Landed in `Molecular/Deficiency.lean`: the matroid `M(G̃)` (boundary-regime
`(D,D)` count matroid), the `D`-deficiency `def(G̃)`, the `k`-dof / minimal-`k`-dof
hierarchy, rigid + proper rigid subgraphs, KT Lemmas 3.1/3.3/3.4, and the **full
def = corank bridge** `|B| + def(G̃) = D(|V|−1)` (JJ [15] Thm 6.1 / Cor 6.2,
`thm:def-eq-corank`, proved in-repo axiom-free). Detail: ROADMAP §19 + notes/Phase19.md.

#### Phase 20 — Combinatorial induction → Theorem 4.9 (§4) — ✓ Complete

Landed the graph operations on `Graph α β` (splitting-off, edge-splitting,
removal, rigid-subgraph contraction) plus the dof-tracking lemmas (4.3–4.8),
the three-case decomposition, and **Theorem 4.9** (every minimal body-hinge-rigid
graph reduces to the two-vertex double edge). KT 4.3 (`def(G̃ᵥᵃᵇ) ≤ def(G̃)`)
proved directly via a deficiency-count partition comparison through `def = corank`,
bypassing the over-quantified forest surgery 4.1/4.2. Detail: ROADMAP §20 + notes/Phase20.md.

#### Phase 21a — Grassmann–Cayley meet / projective-duality foundations — ✓ Complete

Built the Grassmann–Cayley *meet* (regressive product) — the dual sibling of
Phase 17's join — as the substrate for the panel layer's coplanar hinges, Lemma 5.4,
and Phase 25's projective-duality dictionary: `topEquiv` → `pairingDual`-iso →
`complementIso` → `meet` + `meet_ne_zero_iff`. Detail: ROADMAP §21a + notes/Phase21a.md.

#### Phase 21 — Theorem 5.5 base + Cases I & II (§5, §6.1–6.3) — ✓ Complete

Landed the genericity-free content of KT's algebraic induction: the panel layer
(`PanelHingeFramework` → `toBodyHinge` → `IsHingeCoplanar`, gated on the Phase-21a
meet), the Theorem 5.5 induction skeleton + base + the Case I/II genericity-free
reductions, and the analytic half of Prop 1.1 (`rigidityMatrix_prop11`, pinned by
the genericity-free `hub` + a 21b-cited generic-max-rank `hgen`). The shared analytic
crux Claim 6.4/6.9 enters as a cited black-box, scoped out into Phase 21b.
Detail: ROADMAP §21 + notes/Phase21.md.

#### Phase 21b — Genericity device (Claim 6.4/6.9) (§6.1, §6.3) — ✓ Complete

Discharged KT's one genuinely new analytic crux: `lem:genericity-device`
(multivariate Claim 6.4 — `R(G,p)`'s entries are polynomials in the alg.-indep.
panel normals, so a single good realization lifts to a generic one), built on the
multivariate "nonzero minor has a non-root" engine (the `exists_…_polynomial` mirror
bricks via `MvPolynomial.funext`), plus the genericity-free accounting iffs, the
`V(G)`-relative count bridges (N1–N3), and the reusable N7b row/glue infra — all
green + axiom-clean. The math-first pass here re-scoped the realization producers to
Phases 22–23 and corrected the `k=0` split to KT Case III. Detail: ROADMAP §21b +
notes/Phase21b.md.

#### Phase 22 — Realization layer (sub-lettered: 22a + 22b + 22c + 22d + …) (§6.2, §6.4.1)

Opened as a single Phase 22 on 2026-06-04, then **split into sub-phases the same
day** because it over-broadly bundled three independent bodies of work — Track A
(Case I, ~90% green), Track B (Case III at `d=3`, the crux, entirely red), and the
`d=3` assembly. Sub-lettering (22a, 22b, …) keeps the integer phase numbers 23–26
stable; a sub-letter names *one distinct chunk* and is minted only when its turn
comes (Case III at `d=3` itself split: stratum 1 = 22c, the D-candidate crux strata
2–3 = 22d, the `d=3` assembly still unlettered). **22a** = Case I realization
(`notes/Phase22a.md`, ✓ complete); **22b** =
KT Claim 6.4 (the discharge of 22a's green-modulo obligation, `notes/Phase22b.md`,
✓ complete 2026-06-05 — `lem:claim-6-4` fully discharged, so `lem:case-I-realization`
is fully green; the reduction N-22b-1/2/3 cut Claim 6.4 to `htransport`, then the
U1→U4 + route-(i) sequence built the three composing bricks — U3a relabel-leg
transport, **U3b** the genuine crux (exterior projection loses zero rank on a rigid
block), U2/U1 collapse-relabel row reproduction — and the U4 producer composing them);
**22c** = Case III at `d=3`, **stratum 1** (KT §6.4.1, Lemma 6.10, the eq. (6.12)
`+(D−1)` placement, `notes/Phase22c.md`, ✓ stratum-1 complete, opened 2026-06-05
**design-pass-first** — the conjecture's crux, opened on a layer-level design recon,
not a build); **22d** = **KT Claim 6.11**
(the redundant `ab`-row, eq. (6.23)) + its green-machinery prerequisites
(`notes/Phase22d.md`, ✓ complete at the Claim 6.11 milestone, opened 2026-06-05
design-pass-first — the conjecture's hardest single argument; the parked "22c+"
placeholder split into 22c + 22d at 22c open, exactly as 22a→22b+, 22b→22c+); and
**22e** = the candidate-completion + Claim 6.12 disjunction (✓ complete,
closed 2026-06-07; `notes/Phase22e.md`), converting 22d's redundant `ab`-row into the
missing `+1` and discharging the resulting full-rank conditional with the three-candidate
disjunction (closed green-modulo a single N3b duality leaf at the time); and **22f** = N3b,
the point-join↔panel-meet duality leaf `lem:case-III-claim612-line-in-panel-union` (✓ complete
2026-06-07; `notes/Phase22f.md`), which discharged 22e's last red leaf, so Claim 6.12 and the
candidate-completion chain are now fully green. The two target producer nodes
`lem:case-II-realization` / `lem:case-III` stay red (their discharge needs the deferred `d=3`
assembly, not N3b — N10 was a blueprint scope reconciliation). The
`d=3` assembly (`prop:rigidity-matrix-prop11` `hub` + `thm:theorem-55` flip + the
Case-I wiring) is the remaining **deferred, UNLETTERED** successor cut after 22f (it
gets a letter when its turn comes — the crux may itself split). Math for all worked out
in `notes/Phase21b.md` *Finding A/B* + `notes/Phase22d.md` *Hand-off*; the green
Phase-21b infra — device, count bridge, N7b row sub-nodes, splice/union glue — feeds
them.

**Phase 22a — Case I realization (§6.2) — ✓ Complete.** Track A:
the tractable entry point, full-rank, independent of Case III. The composer
`PanelHingeFramework.case_I_realization` (`lem:case-I-realization`) discharges
`theorem_55`'s Case-I branch **green-modulo a single dischargeable hypothesis = KT
Claim 6.4** (the new red node `lem:claim-6-4`, deferred to Phase 22b — the same
green-modulo pattern as Phase 21 → 21b). **Delivered via the block-triangular
reframe.** A coordinator verification pass found the first composer attempt blocked
on a **structural divergence from KT**: it translated KT eq. (6.3)'s
**block-triangular rank-addition** (leg-wise placements, ranks add) into the
project's motion-space **common-seed splice glue** (one placement rigid on both
legs), and three successive bridge hypotheses (`hcrig` → false `hpinc` → too-strong
`htransportGP`) each type-checked but were undischargeable. The fix reproduces KT's
block-triangular structure directly: exhibit `D(|V(G)|−1)` independent rigidity rows
of the *single* common framework `ofNormals G ends q₀`, split block-wise via the
exterior-column projection (the H-block edges ⊔ the surviving edges made independent
by that projection), and read rigidity off the device's independent-row count — no
common placement rigid on both legs. The one deferred obligation is Claim 6.4 itself
(the surviving block's exterior-projected rank at the generic placement, KT
eqs. (6.5)/(6.9)). **Standing lesson:** `DESIGN.md` *Match the source's argument
structure, not just its conclusion* (the common-seed glue type-checked but kept
needing fresh bridge hypotheses to span a gap KT's structure does not have). Full
detail + the hpinc→asymmetric→block-triangular→Qc-non-root design arc:
`notes/Phase22a.md` + `notes/Phase22-realization-design.md` §1.12–§1.16.

**Track A — Case I producer (full-rank, KT §6.2). [22a scope]** Independent of Case III;
reaches full `D(|V|−1)` with no shortfall (the contracted vertex's two
boundary hinges give `+D` via Lemma 5.3 / the splice). Nodes:
- **N4 `lem:rigidContract-isMinimalKDof`** — graph↔matroid contraction-
  minimality bridge. **GREEN** (`rigidContract_isMinimalKDof`, axiom-clean).
  Landed as the Whitney-style sub-build the recon predicted: N4a (0-dof ⟹
  preconnected) → N4b (cycleMatroid under collapse) → N4c (union↔contraction
  bridge `matroidMG_rigidContract_eq_contract`, via rank-saturation + the count
  route) → N4 reconciliation (assemble the green `contraction_isMinimalKDof`
  through N4c + exact collapse vertex-count + def=corank).
- **N5 `lem:case-I-splice-placement`** — splice the inductive legs `(H,p₁)`,
  `(G/E',p₂)` along boundary hinges at panel intersections (eq. 6.6); needs a
  *panel-transversality* lemma (two generic `(d−1)`-panels meet in a
  `(d−2)`-flat) + block-triangular independence (Lemma 5.1). Three KT
  sub-cases (6.2/6.3/6.5). Research-shaped — **decompose math-first** (run the
  constructibility recon).
- **N6 `lem:case-I-realization`** — compose N4 + N5 + the green glue
  (`isInfinitesimallyRigidOn_union_of_inter`) + device ⇒ discharges
  `theorem_55.hcontract`.

**Track B — Case II/III producer at `d=3` (the crux, KT §6.3 + §6.4.1). [22c+ scope]**
This is `theorem_55.hsplit` (k=0 split). The eq. (6.12) degenerate placement
(`p1(vb)=q(ab)` reproduces the `e₀` row; the green N7b-0/1/2/3 + glue feed it)
gives `+(D−1)` — one short — and the missing row is **Lemma 6.10** (`d=3`,
3 candidates `(G,p₁),(G,p₂),(G,p₃)`):
- **Claim 6.11** (combinatorial↔linear): `R(G_v^{ab},q)` has a redundant
  `ab`-row, via Lemma 4.3(ii) + the IH. The hardest non-linear-algebra step —
  wires `M(G̃_v^{ab})` to the row matroid of `R`.
- **Claim 6.12** (extensor-span genericity): if all candidates fail, a nonzero
  `r ∈ ℝᴰ` is ⟂ all extensors on `d+1` generic panels, which by **Lemma 2.1**
  (Phase 17) span `ℝᴰ` — contradiction. The degree-2 condition forces all
  candidates to test the same `r` (eq. 6.44).
- ~12 pages, the single largest proof in the paper; consider an abstracted
  "candidate normal form" lemma to avoid repeating the row-ops three times.

**Process — design-pass-first for Case III (Phase-22 meta-lesson, 2026-06-04).**
Track B / Case III is research-shaped and *interlocking* (Claims 6.11/6.12 + the
candidate framework + the row matroid wired to `M(G̃_v^{ab})`). Per `DESIGN.md`
*Constructibility recon … → Scale-up: design the LAYER, not just the node*: run a
**layer-level design pass up front** (read the whole Case-III argument against KT
§6.4 + the green Lemma 2.1, decide what each piece needs from the shared motive /
candidate structure) **before** grinding it node-by-node. Case I cost ~10
incremental commits before a one-commit design pass surfaced the binding gap (the
too-weak motive); don't repeat that — for Case III, design first.

**Build summary (2026-06-04/05; full detail + decision history in
`notes/Phase22a.md`).** The Case-I producer landed as a chain of green bricks
bounded on the Phase-21b infra: N4 (the Whitney-style contraction-minimality
sub-build N4a→N4b→N4c, green), N6a (non-simple Case I), the **two-motive split**
(a general-position motive `HasGenericFullRankRealization` + forgetful map; bare
`theorem_55` untouched), the (G2) general-position `MvPolynomial` factor, the
N6b/N6c simple Case-I coupling, and the N6 leg-transport `ends`-swap brick. The
composer's IH-shape gap (the IH supplies the *bare* `HasFullRankRealization`, the
coupling needs `HasGenericFullRankRealization`) was closed by the **generic-motive
induction** G2a–c: `theorem_55_generic` re-runs `minimal_kdof_reduction` at the
*conditioned* motive `(G.Simple → GP) ∧ bare`, with only the Lemma-6.3 Case-I legs
needing the generic IH (hard kernel: `G/E(H)` simplicity, `map_simple`,
KT 6.3-vs-6.5). The composer assembly G3a–c then surfaced the structural divergence
(above): the body-set splice's common-seed glue forced undischargeable bridge
hypotheses, fixed by the **block-triangular reframe**, leaving KT Claim 6.4
(`lem:claim-6-4`) as the one green-modulo obligation. **22b** (✓ complete 2026-06-05,
`notes/Phase22b.md`): KT Claim 6.4 fully discharged — the reduction N-22b-2 → N-22b-1
→ N-22b-3 cut it to `htransport`, then the U1→U4 + route-(i) sequence built the three
composing bricks (U3a relabel-leg transport, **U3b** the genuine crux = the
exterior-column projection loses zero rank on a rigid block, U2/U1 collapse-relabel row
reproduction) and the U4 producer composing them into `htransport`; `lem:case-I-realization`
is now fully green.

**Phase 22c — Case III at `d=3`, stratum 1 (KT §6.4.1, Lemma 6.10, the
eq. (6.12) `+(D−1)` placement) — ✓ Stratum-1 complete** (opened 2026-06-05
design-pass-first; stratum-1 producer landed 2026-06-05; crux split out to 22d;
`notes/Phase22c.md`). Track B at `d=3`, the conjecture's crux: the
`theorem_55.hsplit` producer at `k=0`, the single largest proof in KT (~12 pages,
`D = 6`). **Case III at `d=3` is multi-phase** (the user's direction + the recon's
first-chunk cut, `notes/Phase22-realization-design.md` §1.26): Lemma 6.10 partitions
into three difficulty strata, and **22c claimed only stratum 1** — the eq. (6.12)
degenerate placement (`p₁(va)=L⊂Π(a)`, `p₁(vb)=q(ab)`, the `vb`-row reproducing the
`e₀=ab` row → block-triangular with `R(G_v^{ab},q)`) giving `+(D−1)`, i.e.
`rank R(G,p₁) ≥ 5 + 6(|V∖{v}|−1) = D(|V|−1)−1`. Landed green + axiom-clean as
`PanelHingeFramework.case_II_placement_eq612`, composing the green Phase-21b N7b row
infra (N7b-0/1/2/3 + `linearIndependent_sum_pinned_block`) — it sets up the candidate
scaffold the crux completes. Nodes `lem:case-II-realization`, `lem:case-III` **stay
red** — 22c lands the `+(D−1)` brick toward them. **Opened on a layer-level design
recon (five passes), not a build** (Case I burned ~10 node-by-node commits before a
layer pass surfaced the binding gap). KT math: `notes/Phase21b.md` *Finding A/B*,
`notes/Phase22-realization-design.md` §1.25–§1.29.

**Phase 22d — KT Claim 6.11 (the redundant `ab`-row) + its green-machinery prerequisites
— ✓ Complete** (opened 2026-06-05 design-pass-first, re-scoped 2026-06-05 per a fresh user
direction, closed at the Claim 6.11 milestone; `notes/Phase22d.md`). 22d attacked the
conjecture's hardest node — KT **Claim 6.11**, the *missing `+1` row* lifting 22c's
stratum-1 `D(|V|−1)−1` brick toward full `D(|V|−1)` — **bottom-up**, building the
prerequisite chain green + axiom-clean rather than axiomatizing the claim (user override of
the opening axiomatize-as-hypothesis verdict). Claim 6.11's discharge factors, dependency
order, through three combinatorial↔linear gaps — (Gap 2) the matroid-base 4.3(ii) form, a
base `B'` of `M(G̃_v^{ab})` with `|B'∩ãb| < D−1`; (Gap 3) the nested IH-at-restriction
(`G_v = G_v^{ab}−ab` minimal `k'`-dof, `k' ≤ D−2`, eq. (6.22)); (Gap 1) the `M(G̃)`↔row
bridge (eq. (6.23)) — and all three landed green: `lem:case-III-claim-6-11-base`,
`lem:case-III-gap3-minimalKDof`, the analytic seed-rank kernel
(`lem:case-III-seed-rank-bridge` rigidity transfer + `-seed-rank-upper` + `-rank-attainment`,
on KT footnote 6), the full `hub` codimension bound `D+def ≤ dim Z` (discharged on both
consumers), and the redundant-row pigeonhole + row-set identity feeding
**`lem:case-III-claim-6-11`** (the eq.-(6.18)/(6.22)⟹(6.23) discharge). The kernel forced
the **project's first algebraic-independence use** (footnote 6 needs "*this* seed attains
the rank", not "*∃* a seed"; tracker `notes/AlgebraicIndependence.md`, risk #8).
**Claim 6.12 stays de-risked** (extensor-span contradiction on the green Phase-17 Lemma 2.1).
The candidate-completion (eqs. (6.24)–(6.29)), the Claim-6.12 disjunction, and the `d=3`
assembly are the deferred, UNLETTERED successor; its first leaf (eq. (6.28) column-support,
`dualMap_eq_comp_single_proj_of_vanish_off`) landed early under 22d's tail. Nodes
`lem:case-II-realization`, `lem:case-III` stay red. KT math: KT §6.4.1 (Claims 6.11/6.12) +
§4 (Lemmas 4.3(ii)/4.4/4.7/4.8); `notes/Phase22d.md`, ROADMAP §22d.

**The candidate-completion + Claim 6.12 landed in Phase 22e (✓ complete) with its N3b
exterior-algebra leaf landing in Phase 22f (✓ complete) — both fully green; the `d=3` assembly
remains ◷ Planning (deferred, UNLETTERED — gets a letter when its turn comes).** The candidate-completion
(eqs. (6.24)–(6.29)) converting the now-green redundant `ab`-row into the missing full-rank
row (its first leaf, eq. (6.28) column-support, landed early under 22d's tail), the
**Claim 6.12** `D`-candidate disjunction (de-risked, bottoms on the green Lemma 2.1), and
the genericity-free `hub` partition brick of
`prop:rigidity-matrix-prop11` (a Phase-19-partition obligation, **Track-independent**,
itself multi-commit — decompose math-first before scheduling), the `thm:theorem-55`
flip (one-line once the three case producers land), and wiring the fully-green
`case_I_realization` into `theorem_55_generic`'s Case-I branch. Cut deferred exactly as
22a→22b+ and 22b→22c+: name the next distinct sub-phase, do not pre-commit its node list
before its shape is clear.

#### Phase 23 — Case III general `d` + assembly (§6.4.2, §5.2, §7)

**Lemma 6.13**: generalize the `d=3` argument to a length-`d` chain
`v₀…v_d` with `d` candidates and isomorphisms `ρᵢ`; reuse Claim 6.11
and Lemma 2.1 verbatim, generalize the matrix bookkeeping (index-heavy).
Then complete **Theorem 5.5**, derive **Theorem 5.6** (edge-strip to a
minimal `k`-dof subgraph; re-add edges only grows rank; projective
invariance to arrange panels), and state **Conjecture 1.2** as a
theorem.

- **Hard core:** the `d`-fold chain bookkeeping (eqs. 6.59–6.64); the
  genericity/Lemma-2.1 step generalizes cleanly.

#### Phase 24 — 3-D generic bar-joint rigidity matroid

Specialize the dimension-general `Framework V d` (Phase 4) to `d=3`
generic bar-joint frameworks; package the generic rigidity matroid via
`Matroid.ofFun` (Phase 8's linear-matroid framing, now in `d=3`);
define `r(·)` = its rank. **Scope guard:** this is the *linear* matroid
only — no combinatorial/Laman-3D characterization (open per KT §7).

- Mostly reuse; the dim-3 specialization + generic-placement existence
  (à la Phase 8's `exists_uniform_rowIndependent_placement`) is the work.

#### Phase 25 — Projective duality + molecule modelling equivalence

Crapo–Whiteley [4] projective invariance of infinitesimal rigidity in
`ℝ³`; the chain bar-joint of `G²` ↔ hinge-concurrent body-hinge of `G`
↔ panel-hinge of `G` (Whiteley/Jackson–Jordán [13,37]). The geometric
heart of the molecule connection. Likely the hardest of 24–26 (genuine
projective-geometry + the square-graph modelling argument).

#### Phase 26 — Corollary 5.7 (molecule application capstone)

Assemble `r(G²) = 3|V| − 6 − def(G̃)` from Thm 5.6 (Phase 23),
projective duality + molecule equivalence (Phase 25), and the dim-3
rigidity matroid (Phase 24). The protein-flexibility statement /
pebble-game-validity payoff (§1.2). Attribute the rank formula to
Jackson–Jordán [13], conjecture-resolution to KT.

## Reuse map (existing machinery each phase leans on)

- **Phase 4 `Framework.lean`** (dimension-general frameworks, rigidity
  map, infinitesimal rigidity) → Phases 18, 24.
- **Phase 6–8 rigidity matroid / `Matroid.ofFun` linear framing,
  `Mathlib/LinearAlgebra/Matrix/Rank.lean` Gram-det LI mirrors** →
  Phases 18, 21, 24 (genericity / rank arguments).
- **Phase 12 vendored matroid union/submodular
  (`Matroid/Constructions/{Submodular,Union}.lean`)** → Phases 19, 20,
  22 (restriction, contraction, fundamental circuits, union rank).
- **Phase 13 Tutte–Nash-Williams (`BodyBar/TreePacking.lean`)** →
  Phase 19 (`def=0` ⇔ packing; def=corank bridge).
- **Phase 14–16 `BodyBar/{KFrame,Framework,TayTheorem,BodyHinge}.lean`,
  `edgeMultiply`, `bodyBarDim`/`bodyHingeMult`** → Phases 18 (Prop 1.1
  reconciliation), 19 (`G̃`, fibers `ẽ`).
- **Mirror directory `CombinatorialRigidity/Mathlib/`** → Phase 17
  (exterior-algebra / Plücker mirror lemmas are upstream-eligible).

## Risk register / open questions

1. **Grassmann–Cayley depth.** User chose the full symbolic GC algebra.
   Risk: building more abstract machinery than the coordinatized proofs
   need. Mitigation: Phase 17 builds the symbolic layer but lands a
   coordinatized bridge early so downstream phases can stay concrete.
2. **`ℓ = 2k = D` boundary regime** (Phase 19). *Resolved:*
   `matroidMG_indep_iff` confirmed the `D`-fold union + Tutte–Nash-Williams
   covers the boundary regime cleanly; no `CountMatroid.lean` (`ℓ<2k`).
3. **Lemma 5.2 perturbation** (Phase 18). *Resolved:* Phase 18 chose
   the basis-free span-refinement monotonicity form
   (`finrank_infinitesimalMotions_le_of_span_le`) and sidestepped
   analytic rank-semicontinuity entirely — no perturbation argument.
4. **Externals to axiomatize vs prove.** Lemma 5.4 (cycles, [4,34]),
   the [29] pin-a-body fact (Lemma 5.1, *proved* in Phase 18). The [15]
   generic-rank bridge (JJ Thm 6.1 / Cor 6.2) splits: its **matroidal
   half** `def(G̃) = corank M(G̃)` was *proved in-repo axiom-free* in
   Phase 19 (`thm:def-eq-corank`, no deferral); its **analytic half**
   `rank R(G,p) = D(|V|−1) − def(G̃)` lands with Claim 6.4 in Phase 21b.
   User scope is "fully formalize". **Lemma 5.4 decision (2026-06-03):
   formalize, not cite** — as genuine *panel* content (the cycle's
   panel realization with independent hinge extensors = the
   Crapo–Whiteley projective fact), its own sub-phase. Supersedes the
   per-phase cite option for 5.4. See risk #7 + `DESIGN.md`
   *Panel-hinge = hinge-coplanar body-hinge*.
   **Genericity-device decision (2026-06-03):** the shared analytic
   crux Claim 6.4/6.9 (rank/dimension count: matrix entries polynomial
   in alg.-indep. panel coords ⇒ generic max rank) is **scoped out of
   Phase 21 into its own focused sub-phase, Phase 21b** (the analytic
   sibling of 21a). Phase 21 closes on the genericity-free content,
   entering the device as a cited black-box in `lem:case-I`,
   `lem:case-II`, `thm:theorem-55`, `prop:rigidity-matrix-prop11`, and
   the projective assembly of `lem:cycle-realization`. See `DESIGN.md`
   *Genericity device (Claim 6.4/6.9) is its own sub-phase (Phase 21b)*
   + the Phase 21b detail below.
5. **Molecule equivalence primary source** (Phase 25). Whiteley [35] is
   an unpublished preprint; anchor on Jackson–Jordán [13] (Combinatorica
   2008) for the citable result.
6. **General 3-D rigidity is open** (KT §7). The molecule app does NOT
   require it; Phase 24's scope guard must hold or the program balloons.
7. **Panel = hinge-coplanar body-hinge not modeled** (found 2026-06-03,
   mid-Phase-21; **the central modeling correction of the program**).
   KT's panel-hinge framework is a body-hinge framework that is
   *hinge-coplanar* — all hinges at each vertex share a hyperplane
   (KT p.647) — and the conjecture's content is that this constraint
   does not drop rigidity. Phase 18's `BodyHingeFramework` carries the
   *free* (body-hinge) `p` only, so the algebraic-induction statements
   as first drafted (`thm:theorem-55`, the realization-existence nodes)
   prove the **body-hinge** rank theorem — by Prop 1.1 essentially the
   Tay–Whiteley + Phase-19 `def=corank` result already in hand — not the
   conjecture. *Mitigation:* add a **panel layer** — per-vertex
   hyperplanes with hinges derived as intersections (auto-coplanar,
   reuses all rank infra verbatim); state Thm 5.5/5.6 + Cases I–III over
   it. Re-scopes Phases 21–23. Full decision + the (A) predicate vs (B)
   panel-data analysis: `DESIGN.md` *Panel-hinge = hinge-coplanar
   body-hinge*. **Resolved:** the panel layer landed (Phase 21 + the
   Phase-21a meet substrate); Phases 21/21a/21b are complete.
8. **Algebraic independence — relaxation TODO + usage tracker** (found
   2026-06-06, Phase 22d). KT's "generic nonparallel" inductive realization
   = algebraically-independent-over-ℚ coordinates; the project has **avoided**
   it so far (existence/Zariski device + general position — incl. for Claim
   6.4/6.9, 21b/22b), but the **Phase-22d Claim-6.11 kernel** (footnote 6,
   eq. (6.22)) is the **first forced site** (needs "*this* seed attains the
   rank", not "*∃* a seed"). Chosen path: build the alg-independence route to
   green; a candidate **product-route relaxation** (stay in the existence
   formulation at `d=3`) is deferred. **Standing instruction: whenever a new
   alg-independence use is introduced (e.g. Phase 23 general-`d`), add a row to
   the tracker `notes/AlgebraicIndependence.md`** — the single source for the
   relaxation question + every site.

## Opening the next phase

Phases 17–22f + 21a are complete; **Phase 22 (the realization layer) is sub-lettered** —
opened as a single Phase 22 on 2026-06-04, then split the same day into **22a** (Case I
realization, ✓ complete; `notes/Phase22a.md`), **22b** (KT Claim 6.4, ✓ complete
2026-06-05; `notes/Phase22b.md`), **22c** (Case III at `d=3`, stratum 1 = the eq. (6.12)
`+(D−1)` placement, ✓ stratum-1 complete 2026-06-05; `notes/Phase22c.md`), **22d**
(KT Claim 6.11 + its green-machinery prerequisites, ✓ complete at the Claim 6.11
milestone; `notes/Phase22d.md`), **22e** (the candidate-completion + KT Claim 6.12,
✓ complete 2026-06-07; `notes/Phase22e.md`), and **22f** (N3b, the point-join↔panel-meet
duality leaf, ✓ complete 2026-06-07; `notes/Phase22f.md`). The `d=3` assembly is the
remaining successor cut. Sub-lettering keeps the integer phase numbers 23–26 stable.

**Next cut (◷ planning, UNLETTERED): the `d=3` realization assembly.** With N3b green, Claim
6.12 and the candidate-completion chain are fully green, but the two target producer nodes
`lem:case-II-realization` / `lem:case-III` stay red: their discharge is the *realization
assembly* — `prop:rigidity-matrix-prop11` `hub` partition brick (Track-independent,
Phase-19-partition) + the `thm:theorem-55` flip + wiring the fully-green `case_I_realization`
into `theorem_55_generic`'s Case-I branch (this is where the `ofNormals` defeq-timeout trap
bites). Then **general-`d`** (Lemma 6.13) is **Phase 23**. Each gets a letter when its turn
comes. When opening the `d=3`-assembly successor, follow the top-level `CLAUDE.md` *When this
commit opens a phase* protocol and the red-node consistency gate over its target nodes.
