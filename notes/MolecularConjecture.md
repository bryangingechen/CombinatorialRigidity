# Molecular Conjecture — cross-phase program plan

**Status:** IN PROGRESS. Phases 17–18 complete; Phase 19 (`M(G̃)`,
deficiency, `k`-dof) is open (see `notes/Phase19.md`); Phases 20–26
planned. This is the program design for Phases 17–26 and the runbook
for threading the remaining phases.
**Audience:** the agent picking up the molecular-conjecture program.
Read this after `ROADMAP.md` (which carries the one-paragraph program
summary + status row); this file is the lemma-level detail.

When opening each remaining phase, follow the top-level `CLAUDE.md`
*When this commit opens a phase* protocol (create `notes/PhaseN.md`,
sync the user-facing status surfaces, extend `blueprint/src/chapter/
molecular.tex` with the phase's red dep-graph nodes).

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
| 19 | `M(G̃)`, `D`-deficiency, `k`-dof / minimal `k`-dof, rigid subgraphs, def=corank (JJ Thm 6.1 / Cor 6.2); Lem 3.1/3.3/3.4 | §2.5, §3 | 3 |
| 20 | Combinatorial induction: graph ops + forest surgery 4.1/4.2 + 4.3–4.8 + **Theorem 4.9** | §4 | 4 |
| 21 | Theorem 5.5 skeleton + base + **Case I** (6.2: 6.2/6.3/6.5) + **Case II** (6.3: 6.7/6.8) + genericity (Claim 6.4) | §5, §6.1–6.3 | 5 |
| 22 | **Case III, `d=3`** (Lemma 6.10): Claim 6.11 (combinatorial↔linear bridge), Claim 6.12 (extensor-span genericity), 3 candidates | §6.4.1 | 5 |
| 23 | **Case III, general `d`** (Lemma 6.13) → Thm 5.5 complete → **Thm 5.6 → Conjecture 1.2** | §6.4.2, §5.2, §7 | 5 |
| 24 | 3-D generic bar-joint rigidity matroid (linear-matroid form; dim-3 specialization of Phase 4/8) | (J–J [13], Phase 4/8 reuse) | 6 |
| 25 | Crapo–Whiteley projective invariance + molecule ↔ hinge-concurrent body-hinge ↔ panel-hinge equivalence | §1.2 ([4,13,37]) | 7 |
| 26 | **Corollary 5.7**: `r(G²) = 3|V| − 6 − def(G̃)`; the protein-flexibility capstone | §5.2, §1.2 | 6+7 |

**This is a floor of 10 phases.** Phases 18, 21, and 22/23 each carry
enough that one or two may split once inside them (precedent: Phases
8–11 spawned perf/cleanup rounds and structural-edit sub-phases). The
program is the largest single undertaking in the project to date —
comparable in effort to Phases 1–16 combined. Sequence the cut-points
as living estimates; re-cut on contact.

### Per-phase detail

#### Phase 17 — Grassmann–Cayley extensor algebra (§2.1) — ✓ Complete

Done; full detail in `notes/Phase17.md`, dep-graph in
`molecular.tex` `sec:molecular`. Formalized the Grassmann–Cayley /
extensor layer in `Molecular/Extensor.lean`: homogeneous
coordinatization, the affine-independence ↔ top-extensor bridge, the
symbolic extensor/join on `ExteriorAlgebra ℝ (Fin (d+1) → ℝ)`, the
coordinatized Plücker bridge with KT's sign, the affine-subspace
extensor `C(·)`, and the hard core **Lemma 2.1**
(`omitTwoExtensor_linearIndependent` — independence of the `D`
`(d−1)`-extensors of `d+1` affinely independent points), on which Case
III (Phases 22–23) bottoms out. Built the symbolic layer first with a
coordinatized bridge, per the user's full-GC choice.

#### Phase 18 — Panel-hinge rigidity matrix `R(G,p)` (§2.2–2.4) — ✓ Complete

Done; full detail in `notes/Phase18.md`, dep-graph in `molecular.tex`
`sec:molecular-rigidity-matrix`. Built the genuine panel-hinge rigidity
matrix `R(G,p)` in `Molecular/RigidityMatrix.lean` (basis-free: hinge
constraint `S(u) − S(v) ∈ span C(p(e))` + dual-annihilator row block +
null space `Z(G,p) = infinitesimalMotions`), the trivial-motion layer
with the `D`-dimensional / `D·|V|` numeric counts (codimension form of
`rank R ≤ D(|V|−1)`), and the three rank lemmas — 5.1 pin-a-body
(`finrank_pinnedMotions_add_screwDim`), 5.3 parallel-hinges-full
(`eq_of_hingeConstraint_two_parallel`), 5.2 rotation semicontinuity
(`finrank_infinitesimalMotions_le_of_span_le`, the basis-free
span-refinement monotonicity form — see risk #3, resolved). The one
remaining node `prop:rigidity-matrix-prop11` (KT Prop 1.1, reconcile the
rank form with Phase 16's `thm:body-hinge-tay`) was **deferred to Phase
19** — its bridge `def(G̃) = corank M(G̃)` is a Phase-19 object (see the
*Inherited from Phase 18* bullet under Phase 19 below).

#### Phase 19 — `M(G̃)`, deficiency, `k`-dof graphs (§2.5, §3)

`D`-deficiency of a partition `def_G̃(P) = D(|P|−1) − (D−1)d_G(P)`;
`def(G̃) = maxₚ def_G̃(P)`; `k`-dof / `0`-dof (= body-hinge rigid) /
minimal `k`-dof (every base of `M(G̃)` meets every edge-fiber `ẽ`);
rigid + proper rigid subgraph; circuits; 2-edge-connectivity. The
matroid `M(G̃)` and the **def = corank bridge** (the project framing of
JJ [15]'s rank-deficiency identity, Thm 6.1 / Cor 6.2:
`|B| + def(G̃) = D(|V|−1)`).

- **Key reuse:** `M(G̃)` = `(D,D)` count matroid at the boundary
  `ℓ = 2k = D`, = the `D`-fold graphic union of Phase 13/14
  (`unionPow_cycleMatroid` + `tutte_nash_williams`). **Confirm the
  boundary regime `ℓ = 2k` is clean before relying on it** —
  `CountMatroid.lean` is built for `ℓ<2k` and will *not* cover this;
  route through the union construction instead.
- **Inherited from Phase 18:** `prop:rigidity-matrix-prop11` (KT
  Prop 1.1, the reconciliation of the honest rank form
  `rank R(G,p) = D(|V|−1)` =
  `Molecular.BodyHingeFramework.infinitesimalMotions_eq_trivialMotions_iff`
  with Phase 16's reduction-form `thm:body-hinge-tay` /
  `edgeMultiply_isSparse_iff`) was **deferred from Phase 18** to here:
  its bridge is JJ [15] (Thm 6.1 / Cor 6.2)'s `def(G̃) = corank M(G̃)`, a Phase-19
  object, so it cannot land before `M(G̃)`/deficiency. The rank-form
  skeleton it consumes (`def:dof-generic` + the three rank lemmas
  5.1/5.2/5.3) is all green from Phase 18. The conjecture itself needs
  only the upper-bound half (which Phase 16 may already supply); decide
  the prove-vs-hypothesize boundary for the [15] (Thm 6.1) generic-rank
  half when the node lands. Blueprint node `prop:rigidity-matrix-prop11`
  is in `sec:molecular-rigidity-matrix` (red, marked deferred).
- Lemmas 3.1 (2-edge-conn), 3.3 (subgraph minimality via restriction),
  3.4 (circuit ⇒ rigid subgraph) are on the Thm-4.9 critical path; 3.2
  (not 3-edge-conn) and 3.6 (partition decomposition) are off it — 3.6
  is needed only by Case 6.1, schedule with Phase 21.
- New graph ops (splitting-off, edge-splitting, removal, contraction)
  may start here or in Phase 20.

#### Phase 20 — Combinatorial induction → Theorem 4.9 (§4)

Graph operations on `Graph α β`: splitting off `G_v^{ab}` at a degree-2
vertex, its inverse edge-splitting `H_{ab}^v`, removal `G_v`, rigid-
subgraph contraction `G/E'`. The forest-surgery core (Lemmas 4.1, 4.2)
+ the dof-tracking lemmas (4.3–4.8) + the three-case decomposition +
**Theorem 4.9** (every minimal body-hinge-rigid graph reduces to the
two-vertex double edge via splitting-off / rigid-contraction).

- **Hard core:** 4.1/4.2 (explicit forest surgery at a degree-2 vertex
  — no existing analogue, budget the most time); 4.6 (maximal-chain /
  degree-sequence counting guaranteeing the degree-2 vertex); 4.8 (the
  capstone, two circuit-swap arguments). 3.5 (rigid-subgraph contraction
  preserves minimality — Case I engine) lands here or late Phase 19.
- **Reuse:** matroid restriction/contraction + fundamental circuits
  (mathlib `Matroid.restrict`, `Matroid.fundCircuit`), the vendored
  union subsystem (`Matroid/Constructions/Union.lean`), `edgeMultiply`.

#### Phase 21 — Theorem 5.5 base + Cases I & II (§5, §6.1–6.3)

The induction skeleton on `|V|` with hypothesis (6.1) and the
"nonparallel if simple" side condition. Base (`|V|=2`, via Lemma 5.3).
**Case I** (proper rigid subgraph): §6.2 Lemmas 6.2 (non-simple), 6.3
(simple, simple contraction; Claim 6.4 genericity), 6.5 (remaining;
Claim 6.6). **Case II** (`k>0`, splitting): §6.3 Lemmas 6.7, 6.8
(Claim 6.9) — the panel-hinge analogue of Whiteley's bar-joint
1-extension. Cycle Lemma 5.4 ([4,34]) — formalize or axiomatize.

- **Hard core:** Claim 6.4 / Lemma 6.3 genericity ("entries are
  polynomials in alg.-indep. panel coords ⇒ generic point attains max
  rank over the parametrized family"); Lemma 6.8's 1-extension rank
  lift. Rank arguments are block-triangular (reuse Phase 18 Lemma 5.1).
- Broad phase — may split Case I from Case II.

#### Phase 22 — Case III, `d=3` (§6.4.1, Lemma 6.10)

The crux. `k=0`, 2-edge-connected, no proper rigid subgraph: a single
candidate is one row short, so build `D` candidates and show one is
rigid. At `d=3`: three candidates `(G,p₁),(G,p₂),(G,p₃)`.

- **Claim 6.11** (combinatorial↔linear bridge): `R(G_v^{ab},q)` has a
  redundant `ab`-row, via Lemma 4.3(ii) (some base uses `< D−1` copies
  of `ab`) + the induction hypothesis. The single hardest
  *non-linear-algebra* step — wires `M(G̃_v^{ab})` to the row matroid
  of `R`.
- **Claim 6.12** (extensor-span genericity): if all candidates fail, a
  nonzero `r ∈ ℝᴰ` is orthogonal to all extensors on `d+1` distinct
  generic panels, which by **Lemma 2.1** (Phase 17) span `ℝᴰ` —
  contradiction. The degree-2 condition forces all candidates to test
  the *same* `r` (eq. 6.44).
- ~12 pages, the single largest proof in the paper. Consider an
  abstracted "candidate normal form" lemma to avoid repeating the
  row-operation derivation three times.

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
2. **`ℓ = 2k = D` boundary regime** (Phase 19). Confirm the project's
   union/tree-packing covers it before relying on it; do NOT assume
   `CountMatroid.lean` (`ℓ<2k`) applies.
3. **Lemma 5.2 perturbation** (Phase 18). *Resolved:* Phase 18 chose
   the basis-free span-refinement monotonicity form
   (`finrank_infinitesimalMotions_le_of_span_le`) and sidestepped
   analytic rank-semicontinuity entirely — no perturbation argument.
4. **Externals to axiomatize vs prove.** Lemma 5.4 (cycles, [4,34]),
   the [29] pin-a-body fact (Lemma 5.1), [15] generic-rank bridge
   (JJ Thm 6.1 / Cor 6.2). User scope is "fully formalize" — but these are
   cited-not-proved in KT. Re-confirm per phase whether to formalize or
   take as a hypothesis; the conjecture (Thm 5.6) needs the generic-rank
   bridge only for the upper bound, which the project may already supply
   via Phase 16's `edgeMultiply_isSparse_iff`.
5. **Molecule equivalence primary source** (Phase 25). Whiteley [35] is
   an unpublished preprint; anchor on Jackson–Jordán [13] (Combinatorica
   2008) for the citable result.
6. **General 3-D rigidity is open** (KT §7). The molecule app does NOT
   require it; Phase 24's scope guard must hold or the program balloons.

## Opening the next phase

Phases 17–18 are complete and Phase 19 is open (`notes/Phase19.md`,
`deficiency.tex` `sec:molecular-deficiency`, `Molecular/Deficiency.lean`
— all dep-graph nodes red, the forward-mode to-do list). The molecular
program runs **one blueprint chapter per phase** (`extensor.tex` for
Phase 17, `rigidity-matrix.tex` for Phase 18, `deficiency.tex` for
Phase 19 — the former single `molecular.tex` was split in the
post-Phase-18 cleanup round, `notes/Phase18-cleanup.md` J1) and the bib
entries ([4], [29], [15], [2], [13], [37]) are in place. To open the
next planned phase (Phase 20), follow the top-level `CLAUDE.md` *When
this commit opens a phase* protocol: create `notes/Phase20.md` from the
`notes/CLAUDE.md` template (pull the Phase-20 detail above into its
*Lemma checklist* + *Architectural choices*), add a **new**
`blueprint/src/chapter/*.tex` for Phase 20 (per the one-`.tex`-per-phase
convention; its Lean lives in a new `Molecular/` file) with the phase's
red dep-graph nodes as the forward-mode to-do list, flip the ROADMAP
status row to *in progress*, and sync `README.md` /
`home_page/index.md` / `blueprint/src/chapter/intro.tex`.
