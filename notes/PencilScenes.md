# PENCIL-SCENES — the pencil proof against its sources (planning note)

**Status:** queued by the PI on 2026-11-09, ahead of ORIGAMI; unopened, and its number is minted
on open. Same editing discipline as phase notes (≤ 8-line entries, lift cross-cutting lessons).
The read-only recon of §5 is done (2026-11-09; four reports in `notes/pencil-scenes/`).
**Next concrete step:** the open with the PI, who settles the scope (§6) with the recon in hand.

## 1. The PI's words (verbatim)

From an attended session on 2026-11-09. The PI opened it with:

> "I'd like to discuss the proof of the pencil theorem. How should I think of the space of planar
> pictures and liftings with multiple heights? Is there some relation to Maxwell-Cremona lifting?"

The session went on to whether the graphs are arbitrary (Maxwell–Cremona being nicest for planar
graphs) and whether liftings ↔ motions is in Crapo–Whiteley. Checking that against the sources,
the PI added Whiteley 1982, 1984 and 1989 to `.refs/` (§2), then said:

> "I think I'd like to rewrite the proof again or its exposition so that we explain the relation to
> all this context instead of presenting these ideas as if they were new. However, I'm not sure if
> we're ready to open a full-on phase yet. Would it be best if we started recording some notes?"

Asked where to queue it and what to call it, the PI chose "Ahead of ORIGAMI" and "PENCIL-SCENES".

A second session the same day opened with:

> "Let's work on the PENCIL-SCENES notes. I think you can probably dispatch some subagents to do the
> literature review for the existing proof while we discuss intuitions a bit more. Let's maybe work
> through a concrete example."

## 2. What the sources say

Read against the PDFs in `.refs/` (filenames in `REFS.md` *Catalogue of `.refs/`*), first by the
agent of the first session, then by the recon of §5, whose corrections are folded in here. Page
numbers are the printed ones. Bib keys are given where `blueprint/src/bibliography.bib` has one.

- **Crapo–Whiteley 1982** (*Structural Topology* 6, 43–82; `crapoWhiteley1982`). §4, Proposition
  4.1 (p. 70) and Corollary 4.2 (p. 71): panel motions of a polyhedron ↔ stresses of its skeleton.
  Example 4.4 (pp. 72–73): the flat tetrahedron's panel motions are the polyhedra over it. §3.5,
  p. 67, and the caption on p. 56: a **flat pencil** of lines (coplanar and copunctual) spans rank 2.
  §3.6 (p. 68): the rank is projectively invariant; p. 75 asserts it in every dimension, unproved.
  The "sequel" of Example 4.4 is, in their bibliography, "Motions of Trusses and Bipartite
  Frameworks" (`notes/pencil-scenes/ledger-main.md`), so Whiteley 1982 is not to be cited as it.
- **Whiteley 1982**, "Motions and stresses of projected polyhedra" (*Structural Topology* 7,
  13–38; no bib entry). The kinematic proof of Maxwell's theorem. P. 14: lifting a plane picture to
  a polyhedral scene "is an infinitesimal motion of the panel structure". Theorems 3.1 and 3.3
  (pp. 18–21), for abstract **oriented polyhedra** only. That class does not contain S_G (§3), so
  cite it as the origin of the correspondence, not as its general statement. §3.4 (p. 23): the path
  condition. Bow's Proposition 4.4 is on p. 30 (§4.3); K₃,₃ with a crossing as a joint is Example 4.3.
- **Whiteley 1984**, "A correspondence between scene analysis and motions of frameworks" (*Discrete
  Appl. Math.* 9, 269–295; no bib entry). Definitions 2.1–2.4: scenes over a picture of any
  incidence structure S = (V, F; R). Proposition 4.1 (pp. 282–283): eliminating the heights leaves
  the plane plate-and-bar framework L(S(p)); scenes ≅ its motions; Corollary 4.2 compares degrees of
  freedom. Theorems 4.1 (p. 285) and 4.9 (p. 287): inverse maps. §5.1–5.3 (pp. 287–289): the joined
  plate structure and the polarity, how the correspondence was found. **§7.2, Definition 7.2
  (p. 292):** scenes in (K+1)-space over a picture in K-space, one hyperplane per face; flat, folded,
  sharp; "we have not seen this discussed elsewhere". Its Remark: plane pictures of 4-dimensional
  scenes with hyperplane faces give quadratic equations.
- **Whiteley 1989**, "A matroid on hypergraphs, with applications in scene analysis and geometry"
  (*Discrete Comput. Geom.* 4, 75–95; no bib entry). P. 78: the scene conditions are linear in the
  heights. Theorem 3.1 (p. 83): at a generic picture of any incidence structure, incidences are
  independent iff i′ ≤ v′ + 3f′ − 3 on every nonempty subset (Sugihara's conjecture, Sugihara 1984).
  Corollary 3.3 gives the scene dimension in the **independent** case only. §5.1 (p. 87): the polar,
  cutting-plane reading (Crapo's concurrence geometries). Theorem 5.4 (p. 92): plane identified
  body-and-joint frameworks, the independent case. P. 93: the spatial analogue, a conjecture about
  **identified** body-hinge structures with each body's hinges coplanar; p. 94: "the methods used
  here do not extend". Its "[11, Conjecture 2]" (p. 91) is Tay–Whiteley 1984's Conjecture 1.
- **Whiteley 1996** (`whiteley1996`, the author's preprint pages). §8.3: liftings of a picture of any
  incidence structure. **Remark 8.3.2** (pdf p. 45) is the polarity about the paraboloid, taking
  liftings on S to parallel scenes on the dual S\*: not the pencil polarity (§3). Theorem 5.1.3:
  Maxwell's theorem for planar graphs. Theorem A.1.4: the rank formula of a count matroid.
- **Jackson–Jordán 2008** (`jacksonJordan2008pin`; `.refs/` holds the 2006 EGRES report, whose
  numbering is used here; the published numbering is unchecked). **Theorem 7.1** (p. 21): the
  rod-and-pin rank 3|V| − 3 − def(G) for a graph without isolated vertices, proved at pin-collinear
  realizations with generic lines; P_q is their rod-and-pin framework (§5, p. 12). Theorem 7.2(b):
  the multigraph body-and-pin version. Theorem 7.4 re-derives Whiteley 1989 Theorem 5.4. They never
  mention scenes, liftings or L(q).
- **Not in `.refs/`** (references verified in `notes/pencil-scenes/lineage.md`, which has free
  copies): Crapo–Whiteley 1993 and 1994 (Maxwell with cycle conditions; liftings ≅ stresses for
  spherical polyhedra); Sugihara 1984 and his 1986 book (the scene equations; cite the book by
  section); Tay–Whiteley 1984 (`tayWhiteley1984`, now obtainable); Maxwell's "On reciprocal figures
  and diagrams of forces" (1864), which needs a new key, since `maxwell1864` is his stiffness paper.

## 3. The pencil proof's pieces against them

The incidence structure throughout is **S_G**: the points are the bodies, the faces are the closed
neighbourhoods N[v], and w lies on face v iff w ∈ N[v]. The recon's ledgers
(`notes/pencil-scenes/ledger-main.md`, `ledger-d.md`) count the passages that use this material:
in `pencil.tex` and `main-component.tex`, 35 (1 cited, 9 partly cited, 23 uncited, 2 presented as
new); in `pencil-d.tex`, 23 (1, 5, 15 and 2; 14 owe a citation). The main rows:

| Node or passage | Classical source | What the chapter says now |
|---|---|---|
| `sec:main-component-carrier`, `def:pencil-lifting-space` | Scenes: W84 Defs 2.1–2.4; Sugihara 1986 §5.1 | "as in scene analysis"; cites W96 §8.3 only |
| `lem:pencil-lifting-planes-dim` (F(q) ≅ L(q)) | W84 Prop. 4.1's elimination of the heights | uncited |
| `lem:pencil-flat-split`, `thm:pencil-flat-rank`, `thm:pencil-d-flat-rank` | W84 Prop. 4.1, §5.1–5.3; W82 as the origin; the 3 in-plane dimensions are in no source | cites CW82 Ex. 4.4 only |
| `lem:pencil-lifting-planes-motions` (P_q) | W84 Prop. 4.1, Cor. 4.2; JJ's rod-and-pin framework (TR §5) | uncited |
| `sec:main-component-jj`, `thm:pencil-jj-equality` | JJ TR Thm 7.1 over ℝ; W89 Thm 3.1 with the merging lemma (§5, Q1); W89 Thm 5.4, the independent case | cites JJ, no item; calls it JJ's equality "for dim L(q)", which JJ never state |
| `lem:pencil-d-condition-linear` | W89 p. 78 | uncited |
| `lem:pencil-d-rank-collineation`, `lem:pencil-d-rank-scale-shift` | CW82 §3.6, p. 68 | not in this chapter |
| `sec:pencil-duality`, `lem:pencil-self-dual` | The point–plane polarity: KT p. 650, W99 pp. 29–30, CW82 §3.6; TW84 p. 33 names panel and molecular as duals. The self-duality of the pencil class: no source | partly cited, through `lem:polarity-join` |
| "pencil" (`sec:pencil`, `def:pencil-panel-realization`) | CW82 p. 67, "flat pencil"; p. 56, rank 2 | uncited |
| `def:pencil-d-configuration` (d − 2 heights) | No source; contrast W84 §7.2's Remark | unsaid |
| `def:pencil-d-lift` (Part C) | W84 Def. 7.2 at K = 3; a trivial lift is a flat scene | presented as new |
| `sec:pencil-roadmap`, the three introductions | All of the above | no lineage |

New, as far as the recon found (Q3): the pencil stratum itself (no source asks for hinges coplanar
*and* concurrent; ROADMAP §39's 2026-07-23 verdict stands), the pencil realization theorem, the
reduction (A), the main-component induction's steps and coverage (B), C's induction, the
self-duality of the pencil class, and the d − 2 heights over one plane picture. Classical: the
carrier (the scenes over a picture of S_G, both descriptions, both framework readings) and C's lift
space.

## 4. Observations, and the worked examples

The agents' own derivations, checked as marked; check an unmarked one before it goes into a chapter.

- **O1** (holds, `ledger-d.md`). By `lem:pencil-d-rank-scale-shift`, the rank of a configuration
  depends only on the picture q and W, the span of the heights' classes in L(q)/Aff(q), where
  dim W ≤ min(d − 2, def₂) at a main picture.
- **O2.** The universal lift v ↦ ev_v ∈ L(q)* is a configuration in P^{2+def₂} (at a main picture)
  whose closed neighbourhoods each span a plane, and every configuration over q is a linear
  projection of it. If d − 2 ≥ def₂, all general configurations over a fixed main picture are
  projectively equivalent.
- **O3** (the bar condition and the count checked at θ(2,2,3)). Writing h_v(ξ) = g_v·ξ + c_v, the face gradients satisfy
  (g_u − g_v)·(q_u − q_v) = 0: an infinitesimal motion of the bar framework (G, q), where
  Maxwell–Cremona has a stress. Not onto: the rotation fails, by twice each cycle's signed area.
  At θ(2,2,3) the bar framework has 5 motions and the scenes modulo constants 3; the cycle rank is 2.
- **O4** (holds, `ledger-d.md`). Each hinge is affine in each height separately, in every dimension,
  and quadratic in two heights jointly (`notes/pencil/workbook/K-main.md`, MC-3). This is why d − 2
  heights over a plane picture stay linear, where W84 §7.2's hyperplane faces do not.
- **O5** (corrected). The faces of S_G meeting in a line are not just those of adjacent bodies: at
  θ(2,2,3) the faces of the non-adjacent hubs a, b share bodies 1 and 2, and meet along a crease.
  What holds: the edges of G generate the conditions on the face planes (F(q)'s definition), so a
  scene is a function on G's vertices, not on a dual graph, and planarity never enters.
- **O6** (W89 §5.1, re-derived). Read with the points as panel normals, each body's panel meets
  z = 0 in the line with normal (x_v, y_v, 1), the body line of P_q, whatever the heights: every
  configuration over q has P_q as its section by z = 0. The heights tilt the panels about it.
- **O7.** The panel of body v in a configuration is the plane ζ = h_v, and h_v is body v's normal
  velocity in the flex of the flat structure that the heights define (`lem:pencil-flat-split`). So a
  configuration is the flat structure sheared along its own flex, adjacent panels still meeting on
  their hinges; every nonzero multiple of the heights has the same rank.

**The worked example: θ(2,2,3)**, hubs a, b and the paths a–1–b, a–2–b, a–3–4–b (6 bodies, 7 edges;
def₂ = 1, def₃ = def₄ = 0; dim L(q) = 4). At q_a = (−2,0), q_b = (2,1), q_1 = (0,1), q_2 = (0,−1),
q_3 = (−1,2), q_4 = (1,3), the one non-trivial scene is a fold: face a is z = 0, face b is z = x,
creased along x = 0 through q_1 and q_2. Ranks against the deficiency rank: P_q (d = 2) 14 of 14;
flat 29 of 30; an affine height 29; the fold 30 of 30; the fold with a zero second height at d = 4,
50 of 50. A second height first matters at **C₇** (def₂, def₃, def₄ = 4, 1, 0; the smallest graph
under the standing hypotheses with def₃ > def₄): at d = 4, flat 56, one height 59, two 60 of 60.
Both: `python3 notes/scripts/scenes/example.py theta` and `… cycle7` (seed 2).

## 5. The recon (done 2026-11-09)

Four read-only agents, dispatched at the PI's word (§1). Their reports are banked as delivered in
`notes/pencil-scenes/`; this section is their reading, with the coordinator's checks.

- **The ledger** (`ledger-main.md`, `ledger-d.md`): §3's counts and table. Whiteley 1982, 1984 and
  1989 are cited nowhere and are not in the bibliography; the only scene-analysis citation is W96.
- **Q1** (`q1-count.md`): yes. Whiteley 1989's count matroid on S_G has rank 4|V| − 3 − def₂(G) for
  every finite simple G, so W89 Thm 3.1 gives dim L(q) = 3 + def₂(G): a second derivation, without
  KT or JJ. It needs the rank formula of a count matroid (Edmonds–Rota; W96 Thm A.1.4) and a
  **merging lemma** no source read states: parts sharing a face or three points merge without
  raising the sum, after which no body has two neighbours in another part. Equivalently, def₂ equals
  the deficiency counting each part's boundary bodies. Over every infinite field (the agent's
  reading of W89's proof). Evidence: `notes/scripts/scenes/q1_count.py`, `q1_sweep.py`.
- **Q2** (`ledger-d.md`): yes, one lift at a time. Part C's lift space is W84 Def. 7.2's scenes in
  4-space over a picture in 3-space, with S_G's faces. W84 fixes a face's hyperplane, which over a
  plane of base points has a one-parameter slack; the chapter keeps its restriction to that plane.
  The spaces of heights agree. No source names d − 2 heights over one plane picture.
- **Q3** (`lineage.md`): no prior work on the pencil stratum. Nearest: CW82's flat pencil; TW84 and
  Tay 1989 name the coplanar and concurrent classes separately; W99 p. 25 (three coplanar concurrent
  hinges are dependent) and Example 24 (a flat molecule, the zero-height member); the plane analogue
  (W89 Thm 5.4, JJ, Lundqvist–Stokes–Öhman 2025). No source builds a 3-space realization by lifting.
- **Q4** (`lineage.md`, *Summary*): add Crapo–Whiteley 1993 and 1994, Sugihara 1984 and 1986,
  Maxwell's reciprocal-figures paper (a new key) and TW84's pages; optional history (Huffman 1977,
  Mackworth 1973) and Lundqvist–Stokes–Öhman 2025. "Lashed and woven rods" is probably Rigidity
  and polarity II (inferred); low priority.
- **Checked by the coordinator:** W96 Remark 8.3.2 and JJ Theorems 7.1 and 7.2 in the PDFs; W84
  Def. 7.2 against `def:pencil-d-lift`; the merging lemma's proof, step by step; both Q1 scripts
  rerun from `notes/scripts/scenes/`, `q1_count.py` byte-identical. The reports' other page numbers,
  and Q1's field generality, are the agents' readings.
- **Open leads:** the merging lemma's provenance (JJ's rod-and-pin section and W96 Appendix A
  first), before any chapter calls it new; Crapo–Whiteley [CrW4] and Crapo–Ryan [CRy], cited by W96
  near higher-dimensional scenes, unresolved; Crapo–Whiteley 1993's page range (55–78 or 55–79).

## 6. Scope at the open (the PI's call)

- **(a) Exposition.** Chapter prose and citations only: the road map and the three introductions
  say what is classical (§3) and what is new; each row of §3 cites its source; no statement or Lean
  change. A first slice: Whiteley 1982, 1984 and 1989 into the bibliography, cited at the flat rank
  and at `lem:pencil-lifting-planes-motions`; then the rest of §3, Q4's references, and the fixes to
  "JJ's equality for dim L(q)" and to the polarity's attribution.
- **(b) The proof.** State the classical part in its general form (scenes over a picture of any
  incidence structure ≅ motions of the reduced plate framework, W84 Prop. 4.1) and derive the
  chapters' lemmas as its case S_G. Q1 adds an option: present the equality as also following from
  W89 Thm 3.1 and the merging lemma, as a remark, or formalized (W89 §§2–3 and the rank formula; the
  Lean already proves the equality through KT). This may touch the Lean.
- **(c) The observations.** Whether O1–O7 and the worked examples go into the chapters; the road
  map's "Four observations" paragraph is the natural home for O1, O5 and O7.
- **(d) `.refs/`.** Which of Q4's free copies to add (TW84, CW93, CW94, Sugihara's book).
