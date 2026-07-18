# Molecular Conjecture — cross-phase program plan

**Status:** COMPLETE (closed 2026-07-07) — all phases 17–26 (+ 21a/21b,
sub-letters 22a–22l / 23a–23h) done. **The Molecular Conjecture (KT 2011
Conjecture 1.2, conjectured Tay–Whiteley 1984) is formalized at general `d`**:
`PanelHingeFramework.molecular_conjecture` (green + axiom-clean for `6 ≤ bodyBarDim n`, i.e.
`n ≥ 3`) states the panel-hinge ⇔ body-hinge realizability equivalence with genuine hinges,
built on Katoh–Tanigawa's Theorem 5.5 and Theorem 5.6 at full KT strength (all degrees of
freedom, genuine hinges, every dimension `d ≥ 3`) — and **the molecule
application is assembled on top**: the 3-D generic bar-joint rigidity matroid
(Phase 24), projective duality + the molecule modelling equivalence (Phase 25),
and the capstone **molecule rank formula** `r(G²) = 3|V| − 6 − def(G̃)`
(Corollary 5.7, `SimpleGraph.molecule_rank_formula`, Phase 26 — closed
2026-07-07, `notes/Phase26.md`; chapter
`blueprint/src/chapter/molecule-application.tex`, all five nodes green).
The per-phase record lives in the phase table and per-phase detail
blocks below, ROADMAP §17–§26, and `notes/PhaseN.md` — this Status paragraph is a pointer,
not a log (*One canonical home per content type*, `notes/CLAUDE.md`). This file was the
program design for Phases 17–26 and is now the program's frozen record.
**Audience:** an agent reviewing how the molecular-conjecture program was run.
Read this after `ROADMAP.md` (which carries the one-paragraph program
summary + status rows); this file is the lemma-level detail.

The program is closed; this doc is its frozen record and needs no further
boundary syncs. (While the program ran, the rule was: at each molecular
phase boundary, follow the top-level `CLAUDE.md` *When this commit opens /
closes a phase* protocol and keep this doc's phase table, per-phase detail
block, and close-out section current — it is gated by no CI/checkdecls
check, so it drifted unless synced.) Per-phase blueprint nodes live in
that phase's chapter (`extensor.tex` / `rigidity-matrix.tex` / …, or
`algebraic-induction.tex` extensions for the 21/22+ realization layer),
not a single `molecular.tex`.

The *detailed-exposition* deliverable for this program (spelling out the steps
KT's paper compresses, so each crux is followable end-to-end) is tracked in
`notes/BlueprintExposition.md` — the cross-phase ledger of hard nodes that earn
a full followable blueprint proof (most of its entries are
molecular: Lemma 2.1, Prop 1.1's two halves, the Thm-4.9 forest-surgery
track, the Case I/II/III cruxes). During the program the rule was: **capture**
a one-line entry there when a node reroutes and surfaces a stable KT-math
insight, then **write** the prose at that phase's close. The ledger is now
fully written — it reached zero genuinely-pending entries at the post-program
crux-node exposition phase (Phase 27, 2026-07-08), which wrote the four
remaining Case-I cruxes and added a d=3 Case-III worked-case entry.

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

External results KT *cite rather than prove*; the project formalizes
these too — every result the formalization uses is itself formalized
(`DESIGN.md` *Formalize everything the argument uses*), so this list is
the **attribution map**, not a to-cite list. Verified against KT's
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
| 22g ✓ | **The `d=3` assembly: design program + leaf infrastructure** (closed 2026-06-09, `notes/Phase22g.md`; the 22c→22d stratum precedent — banner flips moved to 22h). Pinned the Case-III crux architecture: `case_III_claim612` restated to the premise-free six-join **existential** (the three-fixed disjunction is undischargeable, dim 3 < 6; the producer builds its candidate at the witness join's line). Landed ~15 axiom-clean leaves (the join↔meet bridge, the line-indexed candidate placement, the homogeneous-vector Lemma 2.1 core + consumer restate, splitOff simplicity at `|V|≥4`, the graph-free producer pieces, the GAP-2 bare→generic upgrade). The recon program (design §1.44–§1.49) surfaced + scoped the corrected remaining work — GAPs 1–5: the `|V|=3` triangle base (T1–T4), the `M₃` third-panel dispatch (G4a–G4e, branch-interface verdict (β) = full conditioned IH), the bounded good-`t`, the landed upgrade, and the `IsProperRigidSubgraph` single-vertex predicate repair (G5, first) — all handed to 22h with signatures in design §1.48–§1.49. | §5.1, §6.4.1 | 5 |
| 22h ✓ | **The corrected `d=3` assembly** (closed 2026-06-11, `notes/Phase22h.md`). Took `lem:case-II-realization` / `lem:case-III` green at `d=3` (both pinned to `case_III_realization`): G5 predicate repair, the (β) full-conditioned-IH restate, the `\|V\|=3` triangle floor T1–T4, the `hsplit` producer + the full candidate-placement discharge (W1–W10b), `theorem_55_d3` with the 6.3-vs-6.5 dispatch, the `def=0` Thm 5.5→5.6 stratum, the blueprint close (`thm:theorem-55-d3-instance` green). **Closed green-modulo the named carry family** {`h622`, `h65`, `hbase`, `hsplit`, `hcontract`} (user-adjudicated; design §1.50–§1.55); postmortem: `DESIGN.md` *Statement faithfulness to the source*. | §5.1–5.2, §6.4.1 | 5 |
| 22i ✓ | **All-`k` genuine-hinge motive + reduction-case producers** (closed 2026-06-14, `notes/Phase22i.md`; opened as "the honest all-`k` Theorem 5.5"). Delivered L0–L6: the genuine-hinge all-`k` motive (free-hinge carrier + extensor-in-panel containment — KT's coincident-panel Lemmas 5.3/6.2 are inexpressible with a derived hinge-as-meet), the four-case all-`k` induction (NEW cases: Lemma 6.1 not-2-edge-connected, Lemma 6.8 `k>0` split), and the base / cut-edge / Case-I / Lemma-6.8 producers (`hbase`/`hcontract` discharged). **Re-scoped at close by a deliberate split**; the rest → 22j + 22k. | §3, §5.2, §6.1–6.4 | 5 |
| 22j ✓ | **The shared eq.-(6.12) placement abstraction** (closed, `notes/Phase22j.md`; design §1.68). A span-transport "pinned placement" rank brick (`le_finrank_span_rigidityRows_of_pinned_placement` + augment) the Case-II / Lemma-6.8 producers refactor onto — the L6b producer had inlined a ≈1010-line placement because no shared brick fit the split-off. A two-brick family (Brick A span-rank + the existing `case_III_old_new_blocks` device-feed; Case I stays separate). Consolidated the L6b producer onto it, retired the dead L6a, landed the producer cleanup (dead-code + both stopgap suppressions dropped). | §6.3, §6.4.1 | — |
| 22k ✓ | **Completing the honest all-`k` Theorem 5.5 + Thm 5.6 at `d=3`** (closed 2026-06-16; `notes/Phase22k.md`; layers L7–L10). Discharged the last three 22h carries: Case III rewire (`h622` from the all-`k` IH → `case_III_nested_rank_lower`), the Lemma-6.5 arm (`h65`, via Claim 6.6 + a `def=0` vacuity argument), and the zero-carry spine (`hsplit`; `theorem_55_all_k` / `theorem_55_d3` restated carry-free) — `thm:theorem-55`, `thm:theorem-55-d3-instance` green. Then Theorem 5.6 at `d=3` (`rankHypothesis_of_theorem_55_d3`: spanning-strip + projective-move-free re-add), greening `prop:rigidity-matrix-prop11` (the `def>0` feed) and minting `thm:theorem-55-6-d3`. Consumed 22j's Brick A. | §5.2, §6.1–6.4 | 5 |
| 22l ✓ | **ScrewSpace carrier opacity — d=3 API + migration** (build-time structural-edit refactor; closed 2026-06-16, `notes/Phase22l.md`). Flipped `ScrewSpace` `abbrev`→opaque `def` with a `mk`/`val`/`≃ₗ` API, after migrating the d=3 tree bottom-up along the import spine, cutting the diffuse-typeclass cost behind the surviving `maxHeartbeats` overrides (molecular count 3→1: two caps to default, one 600000→400000). d=3 scope only; general-`d` API deferred to the Phase-23 boundary (unblocks but does not start the "part 2" migration). Recon canonical in `notes/ScrewSpaceCarrier-design.md`. Does not move the math frontier. | — | — |
| 23 ✓ | **Case III, general `d`** (Lemma 6.13) → Thm 5.5/5.6 at general `d` → **Conjecture 1.2 stated as a theorem** (`PanelHingeFramework.molecular_conjecture`, the panel-hinge ⇔ body-hinge realizability equivalence with genuine hinges; green + axiom-clean for `6 ≤ bodyBarDim n`). Closed 2026-07-02; sub-lettered **23a–23h** along the recon's carrier-grade fault line — `CARRIER`=23a (the `screwDim k` spine lift), `CHAIN`=23b–23f (the general-`d` chain dispatch; the member-mapping wall → the KT-faithful `fromBlocks A 0 C D` rank cert (23e) + the dispatch router (23f)), `ENTRY`=23g (KT Lemma 4.6 dichotomy + general extractor + the Lemma 5.4 cycle brick, Crapo–Whiteley fully formalized), `ASSEMBLY`=23h (producer rewire → Thm 5.5 (A2) → Thm 5.6 (A4) → Conjecture 1.2 (A5)). GAP 6 assessed **discharged** at close (the spine's all-`k` IH *is* KT (6.1)). Summary: ROADMAP §23; detail `notes/Phase23{a..h}.md`; recon archive `notes/Phase23-design.md` | §6.4.2, §5.2, §7 | 5 |
| 24 ✓ | 3-D generic bar-joint rigidity matroid (linear-matroid form; dim-3 specialization of Phase 4/8). **Opened and closed 2026-07-06** (`notes/Phase24.md`; chapter `bar-joint-3d.tex`, all eight nodes green; scope guard held — no Laman-3D characterization) | (J–J [13], Phase 4/8 reuse) | 6 |
| 25 ✓ | Crapo–Whiteley projective invariance + molecule ↔ hinge-concurrent body-hinge ↔ panel-hinge equivalence, at rank/motion-space level. **Opened and closed 2026-07-06** (`notes/Phase25.md`; chapter `molecule-modelling.tex`, all 12 nodes green; endpoint theorems `molecular_finrank_motions_eq_square_ker` + `exists_molecular_rankHypothesis_generalPosition`, `Molecular/Molecule/`) | §1.2 ([4,13,37]) | 7 |
| 26 ✓ | **Corollary 5.7**: `r(G²) = 3|V| − 6 − def(G̃)`; the protein-flexibility capstone. **Opened and closed 2026-07-07** (`notes/Phase26.md`; chapter `molecule-application.tex`, all five nodes green; `SimpleGraph.molecule_rank_formula`). Assembled arithmetically from Thm 5.6 (Phase 23), the Phase-25 modelling chain, and the Phase-24 generic matroid via a ≥/attainment leg + a ≤/upper-bound leg over the F4 shadowing carrier (`SimpleGraph.shadowGraph`) | §5.2, §1.2 | 6+7 |

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
assembly, not N3b — N10 was a blueprint scope reconciliation). The `d=3` assembly then split as
its predecessors did: **22g** = its design-program + leaf-infrastructure stratum (✓ complete,
closed 2026-06-09; `notes/Phase22g.md` — the existential Claim-6.12 architecture, ~15 axiom-clean
leaves, the GAPs-1–5 recon program), **22h** = the corrected `d=3` assembly (✓ complete, closed
2026-06-11 green-modulo the named carry family; `notes/Phase22h.md`), **22i** = the all-`k`
genuine-hinge motive + reduction-case producers (✓ complete, closed 2026-06-14, re-scoped at a
deliberate split; `notes/Phase22i.md`), **22j** = the shared eq.-(6.12) placement abstraction
(✓ complete; `notes/Phase22j.md`), and **22k** = completing the honest all-`k` Theorem 5.5 (Case III,
the spine) + Thm 5.6 at `d=3` (✓ complete, closed 2026-06-16; `notes/Phase22k.md`).
Math worked out in `notes/Phase21b.md` *Finding A/B* +
`notes/Phase22-realization-design.md` §1.39–§1.56; the green Phase-21b/22c–22h infra feeds it.

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

#### Phase 23 — Case III general `d` + assembly (§6.4.2, §5.2, §7) — ✓ Complete

**✓ Complete** (opened 2026-06-17, closed 2026-07-02). KT Lemma 6.13 (the
length-`d` chain generalization of the `d=3` Case III) → Theorems 5.5/5.6 at
general `d` → **Conjecture 1.2 stated as a theorem**
(`PanelHingeFramework.molecular_conjecture`). Sub-lettered **23a–23h** along
the recon's carrier-grade fault line: `CARRIER` (23a, the `screwDim k` spine
lift), `CHAIN` (23b–23f — the chain dispatch; the *member-mapping wall*
(intrinsic to KT's moving-member row bookkeeping, eq. 6.62) → the KT-faithful
`fromBlocks A 0 C D` rank certificate (23e) + the dispatch router (23f)),
`ENTRY` (23g — the KT Lemma 4.6 dichotomy + general extractor + the Lemma 5.4
cycle brick `cycle_realization`, Crapo–Whiteley [4]/[34] fully formalized),
`ASSEMBLY` (23h — producer rewire → Thm 5.5 → Thm 5.6 → Conjecture 1.2).
GAP 6 assessed **discharged** at close (the spine's all-`k` IH *is* KT
hypothesis (6.1); `case_III_nested_rank_lower_all_k` derives eq. (6.22) from
it). The hard cores — the `d`-fold chain bookkeeping (eqs. 6.59–6.66) and the
eq.-(6.67) duality finish — are ledgered + written up in
`notes/BlueprintExposition.md` / `case-iii.tex`. One-paragraph summary:
ROADMAP §23; per-sub-phase detail: `notes/Phase23{a..h}.md`; recon archive
(frozen, §-cited): `notes/Phase23-design.md`.

#### Phase 24 — 3-D generic bar-joint rigidity matroid — ✓ Complete

**✓ Complete** (opened and closed 2026-07-06; work log `notes/Phase24.md`;
chapter `blueprint/src/chapter/bar-joint-3d.tex` (`sec:bar-joint-3d`),
all eight nodes green; one-paragraph summary ROADMAP §24). The generic
bar-joint rigidity matroid in linear-matroid form, dimension-general
(`GenericRigidityMatroid.lean`, read at `d=3` by Phase 26): generic
placements + existence, `genericRigidityMatroid` with
placement-independence and the dim-2 reconciliation, `genericRank` +
its rigidity-row-span form. Direct Phase-4/8 reuse throughout; **scope
guard held** — the *linear* matroid only, no combinatorial/Laman-3D
characterization (open per KT §7).

#### Phase 25 — Projective duality + molecule modelling equivalence — ✓ Complete

**✓ Complete** (opened and closed 2026-07-06; `notes/Phase25.md`; chapter
`blueprint/src/chapter/molecule-modelling.tex`, all 12 nodes green). The
`ℝ³` chain bar-joint of `G²` ↔ hinge-concurrent body-hinge (molecular) of
`G` ↔ panel-hinge of `G` (Whiteley [35] / JJ [13,37]), delivered at the
**rank/motion-space level** per the recon's central verdict; projective
invariance (Crapo–Whiteley [4] §3.6) landed as the extensor-transport
family with the polarity already in tree (`complementIso`). Phase 26
consumes the two endpoint theorems
(`molecular_finrank_motions_eq_square_ker`,
`exists_molecular_rankHypothesis_generalPosition`) — the assembly plan +
contract stay live in `notes/Phase25-design.md` §2.2/§2.6. Detail:
ROADMAP §25 + `notes/Phase25.md`; exposition-ledger entries (3, `done`)
in `notes/BlueprintExposition.md`.

#### Phase 26 — Corollary 5.7 (molecule application capstone) — ✓ Complete

**✓ Complete** (opened and closed 2026-07-07; `notes/Phase26.md`; chapter
`blueprint/src/chapter/molecule-application.tex`, `sec:molecule-application`,
all five nodes green). The last phase of the program:
`r(G²) = 3|V| − 6 − def(G̃)` (min degree ≥ 2, `r` = 3-D generic bar-joint
rigidity rank) landed as `SimpleGraph.molecule_rank_formula`
(`Molecular/Molecule/Application.lean`), from Thm 5.6 (Phase 23; `d = 3`
Phase 22k), projective duality + molecule equivalence (Phase 25), and the
dim-3 rigidity matroid (Phase 24). Two complementary bounds — an attainment
(≥) leg (`exists_molecular_rankHypothesis_generalPosition` → dictionary
forward → generic-rank domination) and an upper (≤) leg (generic ∩
general-position placement → `genericRank_eq_finrank_span` → dictionary
reverse → the genericity-free bound `D + def ≤ dim Z`) — over the F4
shadowing carrier `SimpleGraph.shadowGraph` (padded label supply), with
**no new combinatorics** (Thm 5.6's rank statement replaces JJ 2008 §3–4).
The protein-flexibility payoff (§1.2). Rank formula attributed to
Jackson–Jordán [13], conjecture-resolution to KT. Lemma map + decisions:
`notes/Phase26.md`.

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

### Phase 23 — the general-`d` Case III reuse/replace/add map (lifted + source-verified 2026-06-17; Phase 23 closed 2026-07-02 — retained as the record)

KT §6.4.2, p. 692: *"The proof strategy is exactly the same as `d = 3`."* General `d` runs a length-`d`
chain `v₀…v_d` with `d` candidate frameworks `(G,pᵢ)` and isomorphisms `ρᵢ` (eq. 6.54). The full
layer-level recon (sub-phase scope, hard cores, sequence, open decisions) is `notes/Phase23-design.md`;
this block is the program-map summary. Grades below were re-checked against the landed Lean
(2026-06-17), correcting the original §1.33(C) sketch.

| Ingredient | Status for Phase 23 | Note |
|---|---|---|
| **Lemma 2.1** `omitTwoExtensor_linearIndependent_of_li` (`Extensor.lean:563`) | **reuse verbatim — general (`{e:ℕ}`) & GREEN** | the eq. (6.67) span-`D` finish; only the `span_omitTwoExtensor_eq_top` *corollary* is `Fin 4`-stated (re-state at general grade) |
| **Claim 6.11** `exists_redundant_panelRow_ab_of_finrank_eq` (`CaseIII/Candidate.lean:126`) | **reuse verbatim — general (`screwDim k`/`ScrewSpace k`/`Fin (k+2)`) & GREEN** | the chain's redundant `(v₀v₂)_{i*}` row "always exists by Claim 6.11" (p. 693); the single hardest combinatorial piece — done at general grade |
| `linearIndependent_sum_augment_candidateRow` (`RigidityMatrix/Basic.lean:1231`) | **general & GREEN, graph-free** | augments by **one** Unit candidate; the `d`-chain needs `d` candidates → generalize the augment to a `Fin d`-indexed family (CHAIN) |
| `complementIso`/`topEquiv`/`pairingDualEquiv` meet API (`Meet.lean`) | **general & GREEN** (`{j:ℕ}, hj : j ≤ k+2`) | dimension-parametric |
| The realization **spine** — `theorem_55_*`, `case_III_realization*`, `case_III_nested_rank_lower`, the `case_II_*` placement bricks, GenericityDevice/Coupling/CaseI consumers | **`screwDim 2`/`ScrewSpace 2`/`Fin 4`-PINNED** (NOT "`k`-free" — the §1.33(C) sketch was wrong) | **LIFT** to symbolic `screwDim k` = sub-phase **23a** (the mechanical carrier lift; folds in the deferred ScrewSpaceCarrier §6 "part 2" migration) |
| `case_III_candidate_dispatch` (`CaseIII/Realization.lean:181`) | **`d=3`-pinned AND structurally a fixed 3-candidate dispatch** (`v,a,b,c`) | **REPLACE** by the general-`d` chain dispatch (eqs. 6.49–6.64) = sub-phase **CHAIN**; the `d=3` body is the template |
| The **duality** (N3b analog): `⋀²ℝ⁴` → `⋀^{d−1}(ℝ^{d+1})` | **REPLACE** | the 22f `extensor_mem_range_map_subtype_of_mem` / `exists_smul_eq_of_mem_range_map_subtype` (`Meet.lean:648/676`) are `Fin 4`/`⋀²`-PINNED — a **TEMPLATE, not verbatim reuse** (the route rests on general mathlib; re-state at `⋀^{d−1}`). Build LAZILY at concrete grade; **do NOT build a general Hodge star** (KT never needs it — it's the top-power-is-1-dim fact) |
| "same `r`" reduction | NEW but direct — eq. (6.44)/(6.43) → eq. (6.66) "±`r`" chain | the `candidateRow_ac_eq_neg` analog along the chain (CHAIN) |
| `d+1` points in general position (N3a analog), eq. (6.67) | **NEW** — KT uses **alg-independence** (p. 698: `j` hyperplanes meet in a `(d−j)`-flat) | open whether it takes the existence route (as `d=3`'s N3a did, AVOIDED) or forces the alg-independence hammer — **OD-4**, tracked in `notes/AlgebraicIndependence.md` |
| **Lemma 4.6** (chain-or-cycle dichotomy) + **Lemma 4.8** (chain split-off minimal 0-dof) | **OD-2/OD-3 settled 2026-07-01**: 4.8(i) already landed general (`splitOff_isMinimalKDof`); 4.6 NOT subsumed — the genuinely-new combinatorial leaf, **landed** (23g E2, `chainData_or_cycleData_of_noRigid`) | needed to *enter* the chain case (KT p. 692); design §(4.107) |
| **Lemma 5.4** (short-cycle base, `3≤|V|≤D`) | **OD-1 settled 2026-07-01: LOAD-BEARING** (the chain-only extractor is unsatisfiable at general `d` — cycles `4≤|V|≤d` are real); the risk #4 brick **landed** (23g E5, `cycle_realization` — discharges `hcycle`) | genuine panel content (Crapo–Whiteley [4]/[34]); design §(4.107) |

**Build LAZILY (§1.33(D), source-confirmed).** Do **not** build a general Hodge-star / regressive-product
/ star-operator API — KT never needs it; the whole duality is the top-power-is-1-dimensional fact
(`⋀ⁿW` is 1-dim when `dim W = n`). The general route rests on general mathlib (`exteriorPower.finrank_eq`,
`map_injective_field`, `map_apply_ιMulti`) + the project's `topEquiv`/`pairingDualEquiv` mirrors, so the
duality needs only modest mostly-mathlib API at the concrete grade `⋀^{d−1}(ℝ^{d+1})`.

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
4. **External results — all formalized** (no cite/axiomatize fallback;
   `DESIGN.md` *Formalize everything the argument uses*). The record of
   how each landed: Lemma 5.4 (cycles, [4,34]),
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

## Program close

**The program is complete** (closed 2026-07-07): phases 17–26 (+ 21a/21b)
all done, ending at the capstone `SimpleGraph.molecule_rank_formula`
(Corollary 5.7). Phases 22 and 23 ran **sub-lettered** (22a–22l, 23a–23h;
the codes-until-open / mint-a-letter-on-open discipline, which kept the
integer phase numbers 24–26 stable); the per-sub-phase record is in
ROADMAP §22a–§23 and `notes/Phase22{a..l}.md` / `notes/Phase23{a..h}.md`,
with the two design docs (`notes/Phase22-realization-design.md`,
`notes/Phase23-design.md`) left in place as §-cited archives at program
close (blind verdict-compression was assessed inadvisable — dozens of
inbound `§`-pointers from `DESIGN.md` / `notes/BlueprintExposition.md` /
phase notes cite their sections as the sole detailed home). **Updated by
Phase 29's anchor recon (2026-07-09), which refined that disposition per
doc:** `notes/Phase22-realization-design.md` has since compressed by an
anchor-preserving body-shrink (8590 → 1939 lines, twelve slices, zero
repoints, every cited anchor intact — `notes/Phase29.md` W2-7), while
`notes/Phase23-design.md` stays **FROZEN** (137 live Lean-source
doc-comment citations at PROBE/LEAF granularity — `notes/Phase29.md`
W2-8).
`notes/Phase25-design.md` §2.2/§2.6 (the Phase-26 contract) is likewise
discharged and frozen.

The follow-on work beyond the program is post-program **exposition and
organization**, not new mathematics, and is now scheduled as phases
(ROADMAP §27+). The dead-code/liveness sweep of the molecular layer deferred
from `notes/Phase23-cleanup.md` (*Deferred to a future dead-code / liveness
sweep*) ran and closed in the **post-Phase-26 program-closing cleanup round**
(`notes/Phase26-cleanup.md`, 2026-07-07); that round's own deferred follow-on
family — recorded in its *Separately-planned* — is now carved into **Phase 27**
(the remaining crux-node blueprint expositions; opened and closed 2026-07-08,
ledger at 0 pending, `notes/Phase27.md`) and **Phase 28** (RETROSCAN, the
retroactive exposition-coverage scan of the never-scanned non-molecular
phases 1–16 plus the two un-ledgered molecular candidates 22i / 23a, all-OUT,
plus the non-molecular A–F readability sweep; opened 2026-07-08, closed
2026-07-09, `notes/Phase28.md`), and **Phase 29** (RETRO, the Formalization
Retrospective — landed as the blueprint appendix
`blueprint/src/chapter/retrospective.tex` — + the D1 design-doc
compression; opened and closed 2026-07-09, `notes/Phase29.md`). **Phase 30**
(RELAX, the algebraic-independence relaxation — the one genuine math
follow-on; planning note `notes/AlgebraicIndependence.md`, now frozen)
opened 2026-07-09 and closed 2026-07-10: both recons GO and the sanctioned
refactor landed — the proof no longer uses KT's footnote-6 algebraic
independence anywhere (each composition chooses its seed as a non-root of a
finite polynomial product; headline statements unchanged),
`notes/Phase30.md`. **Phase 31** (PROSPECT round 1 — proof-study
simplifications + restructuring recon; survey `notes/Prospect.md`, work
log `notes/Phase31.md`) opened and closed 2026-07-10: the rationality
conjunct dropped from the general-position producers, the `|V| = 3`
triangle base merged into the Lemma-5.4 cycle brick, and two recon
verdicts (the case structure is source-shaped; the planar `D = 3`
analogue is false at `K_{2,3}`, dropping that track). **Phase 32**
(the PROSPECT new-math round: Jacobs' conjecture + the degree-1 rank
formula, both Jackson–Jordán 2008 corollaries on top of the molecule
rank formula; work log `notes/Phase32.md`) opened 2026-07-10 and closed
2026-07-16 — `SimpleGraph.jacobs` and
`SimpleGraph.degree_one_rank{,_tree}` landed, chapter `jacobs.tex`
fully green. **Phase 33** (PROSPECT G1: field generality of the core
Thm 5.5/5.6 chain; work log `notes/Phase33.md`) opened 2026-07-16 and
closed 2026-07-17 — both chokepoint spikes GO and the ℝ→K sweep landed
in 17 slices: Theorems 5.5/5.6 and the molecular conjecture now hold
over any infinite field of any characteristic (the molecule
application stays ℝ). **Phase 34** (PROSPECT G3: the generic lift —
"almost all realizations rigid" via the Jackson–Jordán 2010 coordinate
route; work log `notes/Phase34.md`) opened 2026-07-17 recon-first and
closed 2026-07-18, closing out the PROSPECT queue: the body-bar,
body-hinge, panel-normal, and molecule realization statements now hold
at every generic realization. **Phase 35** (COPLANAR: the full
multigraph strength of Conjecture 1.2 / Theorem 5.6, stated in KT's
own hinge-coplanar panel model — retiring the PROSPECT K1 wall; work
log `notes/Phase35.md`) opened and closed 2026-07-18:
`molecular_conjecture_multigraph` + `theorem_55_6_multigraph{,_gen,_d3}`
landed on the containment-model predicate
`HasCoplanarPanelRealization`, all four
`sec:molecular-coplanar-multigraph` nodes green. Still queued,
codenamed: **PIN** (the 2-d molecular conjecture via Jackson–Jordán
2008's pin-collinear route; unplanned placeholder — the next phase to
open), **UPSTREAM** (mathlib upstreaming) and **VERSO** (the paused
verso-blueprint port).
