# Molecular Conjecture — cross-phase program plan

**Status:** IN PROGRESS. Phases 17–20 + 21a complete (`M(G̃)`,
deficiency, `k`-dof, def = corank bridge, the Theorem-4.9 combinatorial
induction, and the Grassmann–Cayley meet all green; see
`notes/Phase19.md`, `notes/Phase20.md`, `notes/Phase21a.md`). Phase 21
(algebraic induction) has **resumed** with the panel layer green, and
has been **re-scoped to close on the genericity-free content**: the
shared analytic crux Claim 6.4/6.9 (the genericity device) is scoped out
into its own sub-phase **Phase 21b**, entering Phase 21's remaining
nodes as a cited black-box (risk #4/#7 + `DESIGN.md` *Genericity device
(Claim 6.4/6.9) is its own sub-phase (Phase 21b)*). Phases 21b, 22–26
planned. This is the program design for Phases 17–26 and the runbook for
threading the remaining phases.
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
| 21a | **GC meet / projective-duality foundations** (the dual half of §2.1): `topEquiv`, `pairingDual`-iso, `complementIso`, `meet` — the substrate the panel layer + Lemma 5.4 + Phase 25 rest on | §2.1 (dual half) | 1 |
| 21 | Theorem 5.5 skeleton + base + **Case I** (6.2: 6.2/6.3/6.5) + **Case II** (6.3: 6.7/6.8), closing on the **genericity-free** content; **+ panel layer** (coplanar realizations). Genericity (Claim 6.4/6.9) enters as a cited black-box. | §5, §6.1–6.3 | 5 |
| 21b | **Genericity device** (Claim 6.4/6.9): the panel-coordinate parametrization of `R(G,p)` + generic-max-rank argument — the shared analytic crux of Cases I/II, Thm 5.5, Prop 1.1, and the cycle assembly. Discharges the cited black-box left by Phase 21. | §6.1 (Claim 6.4), §6.3 (Claim 6.9) | 5 |
| 22 | **Case III, `d=3`** (Lemma 6.10): Claim 6.11 (combinatorial↔linear bridge), Claim 6.12 (extensor-span genericity), 3 candidates | §6.4.1 | 5 |
| 23 | **Case III, general `d`** (Lemma 6.13) → Thm 5.5 complete → **Thm 5.6 → Conjecture 1.2** | §6.4.2, §5.2, §7 | 5 |
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

Done; full detail in `notes/Phase18.md`, dep-graph in
`rigidity-matrix.tex` `sec:molecular-rigidity-matrix`. Built the genuine
panel-hinge rigidity
matrix `R(G,p)` in `Molecular/RigidityMatrix.lean` (basis-free: hinge
constraint `S(u) − S(v) ∈ span C(p(e))` + dual-annihilator row block +
null space `Z(G,p) = infinitesimalMotions`), the trivial-motion layer
with the `D`-dimensional / `D·|V|` numeric counts (codimension form of
`rank R ≤ D(|V|−1)`), and the three rank lemmas — 5.1 pin-a-body
(`finrank_pinnedMotions_add_screwDim`), 5.3 parallel-hinges-full
(`eq_of_hingeConstraint_two_parallel`), 5.2 rotation semicontinuity
(`finrank_infinitesimalMotions_le_of_span_le`, the basis-free
span-refinement monotonicity form — see risk #3, resolved). KT Prop 1.1
(`prop:rigidity-matrix-prop11`, reconcile the rank form with Phase 16's
`thm:body-hinge-tay`) was originally deferred from Phase 18 to Phase 19;
at Phase-19 close it was **relocated forward to Phase 21+** — its
matroidal half (`def = corank M(G̃)`) landed green in Phase 19, but its
analytic half (`rank R(G,p) = D(|V|−1) − def(G̃)`) depends on the
generic-rank argument (Claim 6.4) and lands with the algebraic induction
(see the *Relocated forward* bullet under Phase 19 + the Phase 21 bullet).
The completed `rigidity-matrix.tex` carries no red node.

#### Phase 19 — `M(G̃)`, deficiency, `k`-dof graphs (§2.5, §3) — ✓ Complete

**Complete; see `notes/Phase19.md`.** Landed in `Molecular/Deficiency.lean`:
`M(G̃)` (boundary-regime `(D,D)` count matroid, clean — risk #2 resolved),
the `D`-deficiency `def(G̃) = maxₚ [D(|P|−1) − (D−1)d_G(P)]`, the
`k`-dof / `0`-dof / minimal-`k`-dof hierarchy, rigid + proper rigid
subgraphs, KT Lemmas 3.1/3.3/3.4 (matroidal-core forms), and the **full
def = corank bridge** `|B| + def(G̃) = D(|V|−1)` (JJ [15] Thm 6.1 / Cor 6.2,
proved in-repo axiom-free — risk #4 resolved, no axiom / no deferral).

- **Key reuse (as planned):** `M(G̃)` routed through the `D`-fold graphic
  union of Phase 13/14 (`unionPow_cycleMatroid` + `tutte_nash_williams`),
  **not** `CountMatroid.lean` (`ℓ<2k`). Confirmed clean by `matroidMG_indep_iff`.
- **Relocated forward at phase close (2026-06-02):**
  - **`prop:rigidity-matrix-prop11`** (KT Prop 1.1, the rank/reduction
    reconciliation) → **Phase 21+**. Its matroidal half (`def = corank M(G̃)`)
    is now green via `thm:def-eq-corank`, but its **analytic half** —
    `rank R(G,p) = D(|V|−1) − def(G̃)` (JJ [15] Thm 6.1 geometric side, wiring
    the rigidity-matrix rank to the matroid corank) — is a separate object
    with no Lean yet, dependent on the generic-rank / genericity argument
    (Claim 6.4) deferred since Phase 15–16. The node was removed from the
    completed Phase-18 `rigidity-matrix.tex`; it gets (re)created in the
    algebraic-induction chapter when Phase 21 opens. Lands with Claim 6.4.
  - **Full KT 3.4** (`G[V(X)]` rigid — the tightness *equality*
    `|X−e| = D(|V(X)|−1)`, vs. the Phase-19 matroidal-core sparse/basis
    form) → **early Phase 20**. Now unblocked: the JJ09 reverse
    `le_rank_add_deficiency` supplies the lower bound `|X| > D(|V(X)|−1)`
    it waited on; still needs a vertex-induced-subgraph-from-edge-set
    construction (no existing `Graph α β` analogue).
  - **KT Lemma 3.5** (rigid-subgraph contraction preserves minimality —
    Case I engine) → **early Phase 20**.
- KT Lemmas 3.2 (not 3-edge-conn) and 3.6 (partition decomposition) remain
  off the Thm-4.9 critical path; 3.6 is needed only by Case 6.1, schedule
  with Phase 21.

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
  capstone, two circuit-swap arguments).
- **Inherited from Phase 19** (relocated at Phase-19 close): KT Lemma 3.5
  (rigid-subgraph contraction preserves minimality — Case I engine) and
  the full KT 3.4 (`G[V(X)]` rigid, the tightness *equality* + a
  vertex-induced-subgraph-from-edge-set construction; the lower bound it
  needs is now green via `le_rank_add_deficiency`). Schedule early.
- **Reuse:** matroid restriction/contraction + fundamental circuits
  (mathlib `Matroid.restrict`, `Matroid.fundCircuit`), the vendored
  union subsystem (`Matroid/Constructions/Union.lean`), `edgeMultiply`.
- **Route change (2026-06-02 — see `notes/Phase20.md` *Finding* +
  *Replan*).** Formalizing the forest surgery (4.1) surfaced that KT's
  Lemma 4.1 is over-quantified (false for `|I| < D`, formally disproved)
  and its proof of the base case glosses an unstated *balanced-packing*
  assumption (every forest in the `D`-forest partition meets `v`) — in
  both the 2011 (Lemma 4.1, p.660) and 2009 arXiv (Lemma 5.1, p.11)
  versions. The induction needs only `def(G̃ᵥᵃᵇ) ≤ def(G̃)` (KT 4.3),
  which is true and which we prove directly by a **deficiency-count
  partition comparison** through `def = corank` (Phase 19), bypassing the
  forest surgery. The surgery (and proving-or-refuting the balanced-packing
  lemma) is a non-blocking TODO; the hard core is now 4.6 / the capstone
  4.8, not 4.1/4.2.

#### Phase 21a — Grassmann–Cayley meet / projective-duality foundations

Inserted by the 2026-06-03 panel re-scope (risk #7). The dual sibling of
Phase 17: where Phase 17 built the *join*, 21a builds the *meet*
(regressive product) — the substrate on which the panel layer derives
coplanar hinges, Lemma 5.4 builds its cycle realization, and Phase 25
inherits the projective-duality dictionary. On `V = ℝ^(k+2)`, route (ii):
`topEquiv` (`⋀ᴺ V ≃ R`) → `pairingDual`-iso (`⋀ʲ(V*) ≃ (⋀ʲ V)*`, the
Phase-25 dictionary entry) → `complementIso` (`⋀ʲ V ≃ ⋀^(N−j) V`, via the
perfect wedge pairing) → `meet` + `meet_ne_zero_iff` (⟺ transversal).
Scope: regressive product only, no metric Hodge; projective *invariance*
→ Phase 25. Items `topEquiv` / `pairingDual`-iso / `complementIso` are
upstream-eligible (mirror directory). Full detail + checklist:
`notes/Phase21a.md`; decision: `DESIGN.md` *Panel-hinge = hinge-coplanar
body-hinge*.

#### Phase 21 — Theorem 5.5 base + Cases I & II (§5, §6.1–6.3)

**Re-scoped 2026-06-03 (panel re-scope, risk #7; genericity scope-out,
risk #4/#7), resumed and building.** Two re-scopes landed this day:
(1) Theorem 5.5 and the realization-existence nodes are stated over
**panel** (hinge-coplanar) realizations, not free body-hinge ones — the
panel layer (`PanelHingeFramework` → `toBodyHinge` → `IsHingeCoplanar`),
gated on the Phase-21a meet, is now green; (2) the shared analytic crux
Claim 6.4/6.9 (the genericity device) is **scoped out into Phase 21b**,
so Phase 21 aims to **close on the genericity-free content** with the
device entering each remaining node as a **cited black-box**. See
`DESIGN.md` *Panel-hinge = hinge-coplanar body-hinge* +
*Genericity device (Claim 6.4/6.9) is its own sub-phase (Phase 21b)*,
and `notes/Phase21.md` *Hand-off* for the node-by-node split.

The induction skeleton on `|V|` with hypothesis (6.1) and the
"nonparallel if simple" side condition. Base (`|V|=2`, via Lemma 5.3).
**Case I** (proper rigid subgraph): §6.2 Lemmas 6.2 (non-simple), 6.3
(simple, simple contraction; Claim 6.4 genericity → 21b), 6.5
(remaining; Claim 6.6). **Case II** (`k>0`, splitting): §6.3 Lemmas
6.7, 6.8 (Claim 6.9 → 21b) — the panel-hinge analogue of Whiteley's
bar-joint 1-extension. Cycle Lemma 5.4 ([4,34]) — its four Lean pieces
are green; the projective assembly is the 21b genericity device.

- **Genericity-free hard core (Phase 21):** the panel layer, the
  block-pin / `withGraph` / `withNormal` framework ops, the
  block-triangular rank *accounting* (reusing Phase 18 Lemma 5.1), the
  edge-substitution bridge, and the `hnew`/`hspan` reduction. The
  *analytic* hard core — Claim 6.4 / Lemma 6.3 genericity ("entries are
  polynomials in alg.-indep. panel coords ⇒ generic point attains max
  rank") and Lemma 6.8's generic 1-extension lift — is **Phase 21b**.
- **Inherited from Phase 19** (relocated at Phase-19 close): the analytic
  half of `prop:rigidity-matrix-prop11` (KT Prop 1.1) — `rank R(G,p) =
  D(|V|−1) − def(G̃)` (JJ [15] Thm 6.1 geometric side), wiring the
  rigidity-matrix rank `R(G,p)` (Phase 18) to the matroid corank
  (`def = corank M(G̃)`, Phase 19's `thm:def-eq-corank`). Its node is
  stated in this phase's chapter `\uses`ing the 21b device; the
  generic-rank conclusion itself lands in **Phase 21b**. Matroidal half
  already green.
- Split realized: Phase 21 = genericity-free reductions; Phase 21b =
  the device. Case I vs Case II may still split within Phase 21.

#### Phase 21b — Genericity device (Claim 6.4/6.9) (§6.1, §6.3)

Scoped out of Phase 21 on 2026-06-03 (risk #4/#7), the analytic sibling
of the Phase-21a meet sub-phase. The one genuinely new analytic crux of
KT's algebraic induction: the entries of the panel-hinge rigidity matrix
`R(G,p)` are polynomials in the algebraically independent panel
coordinates (the per-vertex normals), so the rank is lower
semicontinuous and attains its maximum on a Zariski-open (generic) set —
a single good realization at the target rank lifts to a generic one
(Claim 6.4, and its Case-II twin Claim 6.9). This is the shared
black-box that Phase 21 leaves cited in `lem:case-I`, `lem:case-II`,
`thm:theorem-55`, `prop:rigidity-matrix-prop11`, and the projective
assembly of `lem:cycle-realization`; Phase 21b discharges it once and
the consumers `\uses` it.

- **Scope (at open):** the panel-coordinate parametrization of `R(G,p)`
  (entries as polynomials in the normals), the generic-max-rank lemma
  over that family, and the discharge of each consumer's cited
  hypothesis — `hspan` for Case II (every base-pinned motion lands in
  the two new spans, via the rank count), the block-triangular generic
  gluing for Case I, the cycle projective assembly, and the generic-rank
  reconciliation for Prop 1.1.
- **Reuse to assess on contact:** the Phase 6/8 Gram-det perturbation
  machinery (`Mathlib/LinearAlgebra/Matrix/Rank.lean`,
  `exists_uniform_rowIndependent_placement`-style arguments) is the
  natural candidate; the Phase-21a finding was that the *cycle*
  genericity was purely exterior-algebraic (no perturbation), so assess
  whether the panel-coordinate rank argument is polynomial-perturbation
  or reduces similarly. Bottoms (for Case III's share) on Lemma 2.1
  (Phase 17).
- **Also consumed by Phases 22–23** (Case III's candidate-framework
  genericity, Claims 6.11/6.12) — building it as its own sub-phase pays
  off there too.
- Opens with its own `notes/Phase21b.md` + a blueprint section (likely
  in `algebraic-induction.tex` beside the consumers, or its own chapter
  if it grows); follow the *When this commit opens a phase* protocol.

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
   body-hinge*. Phase 21 is **paused mid-stream** pending this re-scope
   (plan-first, no Lean yet).

## Opening the next phase

Phases 17–19 are complete (`notes/Phase19.md`, `deficiency.tex`
`sec:molecular-deficiency`, `Molecular/Deficiency.lean` — all dep-graph
nodes green). The molecular program runs **one blueprint chapter per
phase** (`extensor.tex` for Phase 17, `rigidity-matrix.tex` for Phase 18,
`deficiency.tex` for Phase 19 — the former single `molecular.tex` was
split in the post-Phase-18 cleanup round, `notes/Phase18-cleanup.md` J1)
and the bib entries ([4], [29], [15], [2], [13], [37]) are in place. To
open the next planned phase (Phase 20), follow the top-level `CLAUDE.md` *When
this commit opens a phase* protocol: create `notes/Phase20.md` from the
`notes/CLAUDE.md` template (pull the Phase-20 detail above into its
*Lemma checklist* + *Architectural choices*), add a **new**
`blueprint/src/chapter/*.tex` for Phase 20 (per the one-`.tex`-per-phase
convention; its Lean lives in a new `Molecular/` file) with the phase's
red dep-graph nodes as the forward-mode to-do list, flip the ROADMAP
status row to *in progress*, and sync `README.md` /
`home_page/index.md` / `blueprint/src/chapter/intro.tex`.
