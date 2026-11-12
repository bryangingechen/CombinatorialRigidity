# PENCIL-SCENES — the pencil proof against its sources (planning note)

**Status:** opened on 2026-11-12 as **Phase 44**, with the PI (§8); the work log is
`notes/Phase44.md`, and this note is the phase's plan and recon record. It was queued by the
PI on 2026-11-09, ahead of ORIGAMI. Same editing discipline as phase notes (≤ 8-line entries,
lift cross-cutting lessons).
The read-only recon of §5 is done (2026-11-09; four reports in `notes/pencil-scenes/`), and on
2026-11-11 the PI settled the scope as (a), exposition only (§6), after §5a's comparison.
Three more recon reports were banked the same day (§5b), and the three papers they asked for
arrived and were read (§5c): the scope stands, the merging lemma's attribution changes.
On 2026-11-11 the PI also settled the plan at the open (§7): the nine calls, a rename in the
Lean, and one more read-only recon, for simplifications of the route, which no recon had asked.
The simplification recon ran the same day (§7a): no to (i), and to (ii) one definition, not one
theorem. The route and the Lean stand; the exposition gains two paragraphs.
**Next concrete step:** `notes/Phase44.md` *Hand-off* (slice 5 or 6; slices 1 and 2 have landed).

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
  Appl. Math.* 9, 269–295; `whiteley1984`). Definitions 2.1–2.4: scenes over a picture of any
  incidence structure S = (V, F; R). Proposition 4.1 (pp. 282–283): eliminating the heights leaves
  the plane plate-and-bar framework L(S(p)); scenes ≅ its motions; Corollary 4.2 compares degrees of
  freedom. Theorems 4.1 (p. 285) and 4.9 (p. 287): inverse maps. §5.1–5.3 (pp. 287–289): the joined
  plate structure and the polarity, how the correspondence was found. **§7.2, Definition 7.2
  (p. 292):** scenes in (K+1)-space over a picture in K-space, one hyperplane per face; flat, folded,
  sharp; "we have not seen this discussed elsewhere". Its Remark: plane pictures of 4-dimensional
  scenes with hyperplane faces give quadratic equations.
- **Whiteley 1989**, "A matroid on hypergraphs, with applications in scene analysis and geometry"
  (*Discrete Comput. Geom.* 4, 75–95; `whiteley1989`). P. 78: the scene conditions are linear in the
  heights. Theorem 3.1 (p. 83): at a generic picture of any incidence structure, incidences are
  independent iff i′ ≤ v′ + 3f′ − 3 on every nonempty subset (W89's own count, p. 76).
  Corollary 3.2, the count with −4 for sharp pictures, is Sugihara's conjecture (1984, p. 92).
  Corollary 3.3 gives the scene dimension in the **independent** case only. §5.1 (p. 87): the polar,
  cutting-plane reading (Crapo's concurrence geometries). Theorem 5.4 (p. 92): plane identified
  body-and-joint frameworks, the independent case. P. 93: the spatial analogue, a conjecture about
  **identified** body-hinge structures with each body's hinges coplanar; p. 94: "the methods used
  here do not extend". Its "[11, Conjecture 2]" (p. 91) is Tay–Whiteley 1984's Conjecture 1.
- **Whiteley 1996** (`whiteley1996`, the author's preprint pages). §8.3: liftings of a picture of any
  incidence structure. **Remark 8.3.2** (pdf p. 45) is the polarity about the paraboloid, taking
  liftings on S to parallel scenes on the dual S\*: not the pencil polarity (§3). Theorem 5.1.3:
  Maxwell's theorem for planar graphs. Theorem A.1.4: the rank formula of a count matroid.
- **Jackson–Jordán 2008** (`jacksonJordan2008pin`; numbering of the 2006 EGRES report, used here).
  The published *DCG* version (in `.refs/` since 2026-11-10) is renumbered, §§1–6, and its text
  has no rod-and-pin framework, so Theorem 7.1 has no counterpart there; its Theorem 5.13 (p. 276)
  is the body-and-pin rank at a pin-collinear realization (not compared with 7.2(b) line by line).
  **Theorem 7.1** (p. 21): the rod-and-pin rank 3|V| − 3 − def(G) for a graph without isolated
  vertices, proved at pin-collinear realizations with generic lines; P_q is their rod-and-pin
  framework (§5, p. 12). Theorem 7.2(b): the multigraph body-and-pin version. Theorem 7.4 re-derives
  Whiteley 1989 Theorem 5.4. They never mention scenes, liftings or L(q).
- **Added to `.refs/` by the PI, 2026-11-10** (read on 2026-11-11, §5b; rows in `REFS.md`):
  Crapo–Whiteley 1994 (liftings ≅ stresses for spherical polyhedra); Sugihara 1983, 1984 and his
  1986 book (the scene equations; cite the book by section); Maxwell's "On reciprocal figures and
  diagrams of forces" (1864), which needs a new key, since `maxwell1864` is his stiffness paper, and
  his 1870 paper; Crapo 1984, 1989, 1991; Rigidity and polarity I, II; Huffman 1977; Mackworth
  1973; Lundqvist–Stokes–Öhman 2025; Rybnikov 1999; and, last to arrive, Crapo–Whiteley 1993
  (Maxwell with cycle conditions) and Tay–Whiteley 1984 (`tayWhiteley1984`), so every source the
  recon asked for is now held.
- **Crapo–Ryan 1986**, "Spatial realizations of linear scenes" (*Structural Topology* 13, 33–68;
  in `.refs/`). §8 (pp. 52–53), for an image of any rank and a family E of "nodes": the
  E-locally linear functions L(E), and the **E-lift**, which adds all of them as coordinates, "that
  preimage of P under projection which is of highest possible rank, given the restriction that no
  node is increased in rank", with a natural projection back to P. Its rank is dim L(E), and
  computing it is the paper's "central objective". With E the closed neighbourhoods of a plane
  picture, L(E) = L(q) and the E-lift is O2's universal lift. No hinges, no rigidity.

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
| `def:pencil-d-configuration` (d − 2 heights) | Crapo–Ryan 1986 §8: the E-lift lifts by all heights at once, and d − 2 heights project it (O2); contrast W84 §7.2's Remark | unsaid |
| `def:pencil-d-lift` (Part C) | W84 Def. 7.2 at K = 3; a trivial lift is a flat scene | presented as new |
| `sec:pencil-roadmap`, the three introductions | All of the above | no lineage |

New, as far as the recon found (Q3): the pencil stratum itself (no source asks for hinges coplanar
*and* concurrent; ROADMAP §39's 2026-07-23 verdict stands), the pencil realization theorem, the
reduction (A), the main-component induction's steps and coverage (B), C's induction, the
self-duality of the pencil class, and reading the lifts by several heights as hinge frameworks
with a rank. Classical: the carrier (the scenes over a picture of S_G, both descriptions, both
framework readings), the lift by all heights at once (Crapo–Ryan's E-lift) and C's lift space.

## 4. Observations, and the worked examples

The agents' own derivations, checked as marked; check an unmarked one before it goes into a chapter.

- **O1** (holds, `ledger-d.md`). By `lem:pencil-d-rank-scale-shift`, the rank of a configuration
  depends only on the picture q and W, the span of the heights' classes in L(q)/Aff(q), where
  dim W ≤ min(d − 2, def₂) at a main picture.
- **O2** (the lift itself is Crapo–Ryan 1986 §8's E-lift, with the closed neighbourhoods as nodes;
  the projection claim is the agents' reading). The universal lift v ↦ ev_v ∈ L(q)* is a
  configuration in P^{2+def₂} (at a main picture) whose closed neighbourhoods each span a plane,
  and every configuration over q is a linear projection of it. If d − 2 ≥ def₂, all general configurations over a fixed main picture are
  projectively equivalent.
- **O3** (checked at θ(2,2,3), `scenes/o3_check.py`; classical in mechanism, §5b). Writing h_v(ξ) = g_v·ξ + c_v, the face gradients satisfy
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
- **O6** (classical: Whiteley 1991 Def. 5.5, §5c; Crapo 1984 §7 with W89 §5.1, §5b; re-derived). Read with the points as panel normals, each body's panel meets
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
  The spaces of heights agree. For several heights over one plane picture, the nearest source is
  Crapo–Ryan 1986's E-lift (Q4), which lifts by all of them at once.
- **Q3** (`lineage.md`): no prior work on the pencil stratum. Nearest: CW82's flat pencil; TW84 and
  Tay 1989 name the coplanar and concurrent classes separately; W99 p. 25 (three coplanar concurrent
  hinges are dependent) and Example 24 (a flat molecule, the zero-height member); the plane analogue
  (W89 Thm 5.4, JJ, Lundqvist–Stokes–Öhman 2025). No source builds a 3-space realization by lifting.
- **Q4** (`lineage.md`, *Summary* and §6): add Crapo–Whiteley 1993 and 1994, Sugihara 1984 and
  1986, Crapo–Ryan 1986 (at O2 and the several-heights configuration), Maxwell's reciprocal-figures
  paper (a new key) and TW84's pages; optional history (Huffman 1977, Mackworth 1973) and
  Lundqvist–Stokes–Öhman 2025. W96's [CrW4], Crapo–Whiteley on 3-stresses and projections of
  4-polytopes, is an unpublished 1994 preprint, one height at a time: not citable. "Lashed and
  woven rods" is probably Rigidity and polarity II (inferred); low priority.
- **Checked by the coordinator:** W96 Remark 8.3.2 and JJ Theorems 7.1 and 7.2 in the PDFs; W84
  Def. 7.2 against `def:pencil-d-lift`; the merging lemma's proof, step by step; both Q1 scripts
  rerun from `notes/scripts/scenes/`, `q1_count.py` byte-identical; Crapo–Ryan's E-lift sentence
  (p. 53), in the agent's text of the scan. The reports' other page numbers, and Q1's field
  generality, are the agents' readings.
- **Open leads:** followed up on 2026-11-11 (§5b).

## 5a. The proof against Whiteley 1984 and 1989 (2026-11-11)

The session agent's reading of W84 §§2–5 and W89 §§2–3 in the PDFs beside `main-component.tex`'s
carrier, flat-rank and equality sections; F(q) checked against the definition's body. It sharpens
§3's rows.

- **Two eliminations of one system.** The scene equations have unknowns (heights, face planes).
  L(q) keeps the heights: W89 §2 (p. 78) and the derived 4-hypergraph H(S) of Thm 3.1. F(q) keeps
  the planes: W84 Prop. 4.1's reduced plate framework L(S(p)). `lem:pencil-lifting-planes-dim` is
  W84 Prop. 4.1 composed with W89 p. 84, step (a) ⇔ (c), whose assumption (three non-collinear
  points on each face) is admissibility. §3 credits W84 alone, and no row names W89 for L(q).
- **F(q) is L(S_G(q)) for one row reduction.** W84 reduces at each vertex w to a fan of bars on
  the line (x_w, y_w, 1) joining the faces through w (p. 282); any fan gives a line-equivalent
  framework (p. 283). The star from face N[w] to each N[u], u adjacent to w, gives
  h_u(q_w) = h_w(q_w), which over all w is F(q)'s condition. A bar is a line, and its equation is
  d · (M_j − M_k) = 0 (p. 277).
- **L(S_G(q)) is pin-collinear.** Each edge uv gets two bars between plates u and v, on the lines
  (x_u, y_u, 1) and (x_v, y_v, 1): a pin at their meet, with all of plate v's pins on its own
  line. So W84's reduction of S_G lands in Jackson–Jordán's class; this is the link between
  scenes and P_q that `sec:main-component-jj` asserts without a source.
- **The flat split is W84 §5.1 and three more dimensions.** The joined plate structure (p. 288):
  plates in z = 0 with vertical velocities ux + vy + w that agree at joints, the W_Π part of
  `lem:pencil-flat-split`. The three in-plane dimensions are the chapter's. §5.3 (pp. 288–289):
  the heights of the scene are the joints' velocities (O7).
- **W84 names the gap the equality fills.** Remark 2 (p. 287): the generic theorem for frameworks
  "assumes that any two bars can, generically, be in different directions", so it does not cover
  identified frameworks such as L(S_G). W89 Thm 3.1 is the independent case, Jackson–Jordán the
  rank. `thm:pencil-jj-equality` is better titled as the dimension of the scene space of S_G.
- **Field** (the agent's reading of W89 pp. 80–81, unchecked by a second reader): Thm 2.3's proof
  specializes a matrix of indeterminates, so it holds over every infinite field.

## 5b. The second recon (2026-11-11)

Three read-only agents, their reports banked as delivered in `notes/pencil-scenes/`:
`merging-lemma-provenance.md`, `refs-liftings.md` and `refs-polarity.md`, the last two on the
references of 2026-11-10. Each report ends with a table of citation changes per row of §3; those
tables are the exposition phase's worklist. This section is their reading.

- **The merging lemma** is in no source this recon read (its face merge is in Berg–Jordán 2003,
  §5c), and no stated result specializes to it. Its identity
  follows from JJ TR Thm 7.1 through W84 Prop. 4.1, W89 Thm 3.1 and the Edmonds–Rota formula, a
  chain no source assembles (the agent's inference). So: the identity "follows from" JJ and is
  "not found stated"; the merging argument is ours, by the union defect of a count (Lovász–Yemini;
  Jordán 2016 Lemma 2.1.2, Thm 2.3.2) and |P ∪ N(P)| = |P| + d(P) (JJ's molecular paper,
  Thm 3.4). JJ say twice that a direct proof exists and write none (TR pp. 9, 22).
- **W89 Thm 3.1 over every infinite field:** confirmed by the agent on the page images, and by
  the session agent's reading (§5a).
- **O6 is classical.** Crapo, "Concurrence geometries" (*Adv. Math.* 54 (1984) 278–301), §7,
  Theorem 4 (pp. 293–294): hyperplanes with given sections on a fixed hyperplane, one scalar each,
  concurrence linear in the scalars; W89 §5.1 (p. 87) identifies them with scenes. Reading the
  panels as a body-hinge framework with a rank stays new.
- **Several heights are named before Crapo–Ryan.** Crapo 1984 p. 295: a fixed flat of corank p,
  "We shall not deal further with this generalization". At p = d − 2 it is the polar form of
  `def:pencil-d-configuration` (the agent's algebra, unchecked). No source of the liftings cluster
  lifts by more than one height.
- **O3 is classical in mechanism.** The perpendicularity is the gradient-space rule (Maxwell 1870
  pp. 7–8; Mackworth 1973 p. 125; Huffman 1977 p. 479; CW93 Thm 4.5(a); CW94 Prop. 4.1); the face
  diagram as a motion is CW94 Remarks 2.8 and 3.2. Specific to S_G: the diagram lives on G, not
  on a dual graph, which is why it is a motion where Maxwell–Cremona, through planar duality, has
  a stress (CW94 Thm 3.1).
- **Sugihara 1984 co-originates the carrier** (§§2.2, 3.1: the scene equations of any incidence
  structure and their dimension; p. 84, the equal dimensions of `lem:pencil-lifting-planes-dim`;
  eq. (10), p. 85, the scale-and-shift map at d = 3). Cite it beside W84.
- **The self-duality of the pencil class** is stated nowhere, and follows from Rigidity and
  polarity I §4 (Thm 4.1, p. 345: a point–plane incidence class and its polars have identical
  static properties) with S_G self-dual (the agent's derivation, exact for nondegenerate
  realizations). The agent would say "an immediate consequence, not stated in the sources".
- **Smaller answers.** Lundqvist–Stokes–Öhman's Theorem 4.1 is rigidity of rod configurations, no
  rank formula: an extension of W89 Thm 5.4, not the plane rank statement. "Lashed and woven
  rods" is very likely Rigidity and polarity II (by content). TW84 p. 34: "Only in 3-space does
  projective duality convert a hinge structure to a new hinge structure". CW93 runs pp. 55–78.
  The pencil stratum stays new; nothing contradicts O1–O7. Corrections to `lineage.md`: TW84's
  bibliography has 12 entries, and the two polarity papers' subtitles (`refs-polarity.md` §11).
- **Checked by the coordinator:** JJ TR pp. 9 and 22; Crapo 1984 pp. 294–295; CW93's last page
  (the margin digit and the bibliography); W89 pp. 82–83 for the two counts; W84 §7 (pp. 291–293)
  against `def:pencil-d-lift`, where only Def. 7.2 transfers, since the base of a Part C lift is
  a special-position picture; `o3_check.py` rerun. The rest are the agents' readings.
- **Open, the PI's calls.** The wording for the self-duality. Untested: whether Crapo 1989's
  Euler characteristic gives 3 + def₂ on S_G, a third route to dim L(q), which needs a committed
  script. (The three papers this entry asked for are held and read, §5c.)

## 5c. The three fetched papers (2026-11-11)

The PI added Berg–Jordán 2003, Imai 1985 and Whiteley 1991 to `.refs/` (rows in `REFS.md`; also
Jordán 2023, ORIGAMI's single-block rank formula). The session agent read all three whole, in the
text layers, and Whiteley 1991 pp. 291–293 on the page images. No second reader. M1–M3 are the
merging lemma's three parts, as `merging-lemma-provenance.md` §0 names them.

- **Berg–Jordán 2003 holds the face merge.** §4 (p. 85): the count |E′| ≤ d|A(E′)| + |B(E′)| − d
  on a bipartite graph, which at d = 3, with A the faces and B the points, is W89's. Theorem 3
  (p. 85, credited to W89): the partition criterion for full rank, "by calculating the rank
  function". The Claim in Theorem 4's proof (pp. 85–86) displays the union identity (M1) and
  merges classes that share a vertex of A: "we can assume that A(E_i) ∩ A(E_j) = ∅" (M2).
  Inequality (6) is then M2's deficiency, counted on the points lying in two or more classes.
- **Not in it:** the three-point merge (M3; their identity gives it at once, but they use only a
  shared vertex of A), S_G or any family of closed neighbourhoods, and def₂. So §5b's verdict
  changes for M1 and M2 alone, from "same technique for a different statement" to "stated for
  this count, inside a proof". "No source states the identity" stands.
- **The attribution sentence** (provenance report §9) keeps its first half: the identity follows
  from JJ and is not found stated. Its second half changes: the face merge is Berg and Jordán's
  (their Claim, proving that 2d-connected bipartite graphs are d-tight by Lovász–Yemini's
  approach); ours are the three-point merge on S_G and the value 4|V| − 3 − def₂(G).
- **Imai 1985 holds neither.** Its count is Sugihara's, with −4, and §3 (p. 81, Fig. 1) shows it
  defines no matroid. Eq. (5.1) (pp. 86–87) is the rank formula of a count matroid, from Welsh's
  *Matroid Theory* §8.1; Theorem 5.1 (p. 88): the same min–max fails for the −4 count. So the
  second derivation has to stay with W89's −3 count, as `q1-count.md` does. Nearest item:
  Theorem 4.1 (p. 83), for a plane drawing, c-regular implies the face graph is independent in
  the 2|F| − 3 count. A different statement.
- **Whiteley 1991 is O6's setting, for any incidence structure.** Definition 5.5 (pp. 291–292):
  a section diagram assigns a plane line to each face, and a scene lifts it if each face plane
  meets the x–y plane in its line. P. 292: "If we polarize the pictures and the scenes, we obtain
  the polar theorem for generic section diagrams" (Corollary 5.7). O6 is this polarization at
  S_G: cite it first, then Crapo 1984 §7 and W89 §5.1. Theorems 3.5 and 3.7 (pp. 283–284),
  sections and self-stresses of the grillage, need a spherical polyhedron (Remark 3.8): not S_G.
- **Bibliographic.** Whiteley 1991 is volume 32 (printed on p. 275): CW94's [14] is right, CW93's
  [29] wrong. It prints the counts of Theorem 5.6 and Corollary 5.7 interchanged (3|V| + |F| − 4
  for pictures), against its own p. 292 and W89 Cor. 3.2: cite W89 for the count.
- **Unchecked.** Whether (q, P_q) is a section-projection figure in Whiteley 1991's sense
  (Def. 5.2, p. 288). There one scene is both sectioned and projected; O6 sections the polar of
  the scene over q. Check it before a chapter says so.
- **What changes in the plan.** Nothing in §6's scope. §5b's fetch calls are closed; the
  worklist gains these citations; the second derivation, if written, credits Berg–Jordán.

## 6. Scope at the open

**PI, 2026-11-11:** asked "How much value would scope (b) have for formalizing future results in
this area?", and to the answer recorded below, "OK, let's go with your recommendation."

- **The scope is (a), exposition only**, written in the general language (the incidence structure
  S_G, scenes, the picture matroid), so that a later generalization changes no exposition. No
  statement or Lean change. §5a's corrections join (a)'s list.
- **(b) is not done here.** Of its three pieces: scenes ≅ motions of the reduced plate framework
  in general form has no future consumer, so it is cited, not formalized. The scene space over a
  general incidence structure, with its genericity lemmas, is a candidate first layer of ORIGAMI,
  decided at ORIGAMI's opening recon (`notes/Origami.md`). The picture matroid (W89 Thms 2.3 and
  3.1) is a backlog entry (`notes/IdeaBacklog.md`, Tier B), IDENT-PANEL's prerequisite at d = 2.
- **(c) and the equality's second derivation** are settled in §7 (calls 2 and 3). §5b and §5c
  give the attribution each carries: O3 and O6 are classical; of the merging argument, the face
  merge is Berg–Jordán's and the three-point merge on S_G is ours, its identity a consequence of
  published theorems.
- **The scope widened on 2026-11-11 (§7):** one rename in the Lean, and whatever the
  simplification recon's first question returns. No statement changes. It widened again at the
  open (§8): docstrings, and the flat split in every dimension, which restates one node.

The options as they stood before the decision:

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
- **(d) `.refs/`.** Mostly settled: the PI added CW94, Crapo–Ryan, Sugihara's book and Q4's
  optional items on 2026-11-10 (§2). Left: TW84 and CW93, both free.

## 7. The plan at the open (2026-11-11)

From an attended session. The session agent sketched the exposition and nine recommendations; the
PI asked whether the Lean had the right definitions and which names should change, then:

> "Let's include the rename in this phase."

> "we've done a few recons in this phase but I don't remember if we've been keeping an eye out
> for any simplifications / improvements we could make to the current route. Do you think
> there's any potential for that?"

> "Let's add this to the plan for the phase. I think I'll run it in the next fresh session. I
> went over your recommendations in your earlier message and they look good. Let's keep those,
> but I guess some of them might become outdated depending on how much we end up adjusting the
> route."

**The exposition.** The carrier section of `main-component.tex` names S_G and says L(q) is its
scene space (W84, Sugihara 1984); `lem:pencil-lifting-planes-dim` compares the two eliminations
(§5a); P_q is W84's reduced plate framework of S_G, pin-collinear; the flat rank credits W84
§5.1; the equality is attributed as in §5a. `pencil-d.tex`: the sources of §3's rows, with
`def:pencil-d-lift` no longer presented as new. `pencil.tex`: "pencil" and the polarity. The
road map and the three introductions get a lineage paragraph and what is classical and new.

**Slices,** one commit each: the open; the carrier section with its bibliography entries; the
flat rank and the equality; `pencil-d.tex`; `pencil.tex`; the road map and introductions (last,
and attended, as it sets the framing); the additions of calls 2 and 3; the rename; the close.
Slices between the open and the road map can run under `/coordinate-phase`. A bibliography
entry lands with the slice that cites it (`lint.sh` check 2).

**The verification rule.** Each slice re-reads every page it cites in the PDF. Four derivations
are unchecked and go into a chapter only once checked in their slice, or weakened: the
self-duality from Rigidity and polarity I; O2's projection claim; Crapo 1984 p. 295 as the
polar form of `def:pencil-d-configuration`; (q, P_q) as a section-projection figure (§5c).

**The nine calls** (the session agent's recommendations, kept by the PI; revisit each against
the simplification recon's result):

1. The self-duality: "a consequence of Whiteley's Theorem 4.1 (Rigidity and polarity I) and the
   self-duality of S_G; we have not found it stated", for nondegenerate realizations, if the
   derivation checks.
2. The second derivation: a short remark, no proof in the chapter. The equality is W89's count
   on S_G; the identity follows from published theorems and is not found stated. The merging
   argument stays in `notes/pencil-scenes/q1-count.md`.
3. The observations: O7 and O1 join the road map's observations; O3 and O5 make one remark on
   Maxwell–Cremona (a motion of the bar framework on G, not a stress, as the diagram lives on G
   and not on a dual graph); O4 is a sentence at the configuration definition; O2 and O6 only
   if their unchecked parts check; θ(2,2,3) is one worked example in the carrier section, C₇ a
   sentence.
4. "Lifting space L(q)" stays the chapters' term, introduced once as the scene space of S_G.
5. "Jackson and Jordán's equality" (17 uses in the three chapters, prose in 7 Lean files) is
   renamed in prose to the dimension of the lifting space, Jackson–Jordán credited in the body.
6. A second bibliography entry for Jackson–Jordán's 2006 EGRES report, where Theorem 7.1 is.
7. History cited: Maxwell 1864 and 1870, Sugihara, Whiteley, Crapo, Crapo–Ryan; Huffman and
   Mackworth only with the O3 remark; Falk 1972 and Duda–Hart 1973 (unread) not cited; Rybnikov,
   Lundqvist–Stokes–Öhman and Crapo 1989, 1991 only where a sentence needs them.
8. The third route (Crapo 1989's Euler characteristic) is a backlog line (`notes/IdeaBacklog.md`).
9. The run: `/coordinate-phase` for the middle slices, the road map slice attended.

**The Lean.** The definitions are the classical ones at S_G (`Graph.liftingSpace` keeps the
heights, `Graph.liftingPlanes` the face planes, `Graph.affineLifts` the trivial scenes;
`liftSpace` and `IsTrivialLift` are W84 Def. 7.2's scenes and flat scenes), so none changes. The
rename: Part C's `liftSpace` (39 uses in 6 files), one syllable from `liftingSpace`, a
different object. Its new name is `baseLiftSpace` (§8). Not renamed: `liftingSpace` (W96's word;
ORIGAMI's general scene space is the moment), `affineLifts`, `IsTrivialLift`. Docstring citations
change in this phase, with call 5 (§8). The `x0` in names and labels, a leftover working name,
is uncounted and a cleanup round's.

**The simplification recon** (read-only, before the open): done, §7a. It asked (i) whether a
Part C lift is a motion of the panel structure below, so that `lem:pencil-d-ear-free` follows
from a rigidity statement, and (ii) whether the flat split and the lift space share one
statement. Two weaker leads stay backlog lines: the universal lift at d − 2 ≥ def₂ for the
every-dimension coverage's large cases, and O7's shear as a first-order argument for the gap.

## 7a. The simplification recon (2026-11-11)

Two read-only agents, one per question, both at Claude Mythos 5.2 through the unpinned `recon`
definition, which inherits the session's model (there is no Mythos-pinned definition; adding one
is `/harness-review`'s). Reports banked as delivered: `notes/pencil-scenes/simplify-i.md` and
`simplify-ii.md`. This section is their reading, with the coordinator's checks.

- **(i): no.** A Part C lift is not a motion of the panel structure in 3-space, and "every lift
  is trivial" neither gives nor follows from rigidity there. A lift has 3 unknowns per body and
  2 conditions per edge, the plane count; W84 §7.3 (p. 293) says the reduction to a framework
  "is undefined for K = 3". At general points, C₅ and C₆ are rigid with non-trivial lifts and K₂
  flexes with none (`notes/scripts/scenes/lift_cycles.py`). `lem:pencil-d-ear-free` keeps its
  proof, every `\uses` included, and no Lean change comes from (i).
- **What (i) gives the exposition.** The correspondence that holds is in the Lean already
  (`exists_pencilConfigPoint_of_dotProduct`, `mem_liftMaps_pencilConfigPoint_iff`): the lifts of
  r⁰ are the scenes over its plane projection q′, so motions of P_q′ by W84 Prop. 4.1. Trivial
  lifts are Aff(q′) ⊕ K·z′, and "every lift is trivial" says dim L(q′) = 4: P_q′ has exactly one
  non-trivial motion, the base's own height.
- **(ii): one definition, not one theorem.** L(q) and the lift space are the scenes of S_G over
  points of K³ and of K⁴ (W84 Def. 7.2 at K = 2 and 3; `liftSpaceTilde` is the K⁴ case
  literally). The flat split, scenes as normal motions, is special to plane pictures: a face
  form has n coordinates and a screw C(n+1, 2), equal only at n = 3. At a general configuration
  of C₇ the base has 3 non-trivial lifts and its flat lift to d = 4 one non-trivial motion.
- **(ii) in the Lean:** no declaration of `Grade/Lift.lean` or `Grade/Flat.lean` would become an
  application of a shared motion statement. A shared scene-space definition over `Fin n` and a
  face family is the agent's estimate of 200–300 lines of net growth; nothing for this phase.
  For ORIGAMI's opening recon: two independent axes, the face family (ORIGAMI's, at n = 3) and
  the ambient dimension (Part C's only); see `simplify-ii.md`, Step 3(b).
- **One lead that would touch the Lean** (the agent's, partly checked): the every-dimension flat
  rank is proved by padding and never uses the flat split, and the d = 3 flat rank is its case
  m = 1, so the flat motion count (about 120 lines of `MainComponent/Flat.lean`) could retire,
  if the import order is turned. It would delete the Lean of `lem:pencil-flat-split`, the one
  place the chapters formalize W84 §5.1. The coordinator would keep it, and have the chapter
  say that the every-dimension flat rank does not go through it. Six further duplications
  between `MainComponent/` and `Grade/` are in `simplify-ii.md`, unverified: a cleanup round's.
- **Checked by the coordinator:** the bodies of `liftSpace`, `IsTrivialLift`, `liftSpaceTilde`,
  the statements of `mem_liftMaps_iff` and `finrank_infinitesimalMotions_map_injective`; W84
  p. 293's two sentences, in the text layer; `lift_cycles.py` and `example.py cycle7` rerun,
  figures as reported (on a cycle every ζ is a lift, which gives the first column by hand); the
  every-dimension flat rank's proof; no use of the flat motion count or `linkConstants` outside
  `MainComponent/Flat.lean`, while `flatPi` and `planarProj` serve the joins and `Lines.lean`.
- **Not checked:** the agents' derivations (the normal-velocity obstruction, the splitting in
  4-space, the lift by 0 as `F.map screwEmbed`, C₇'s configuration as a legitimate Part C base);
  the line-count estimates; the other leads at the end of each report.
- **The PI's calls at the open** (settled, §8): `pencil-d.tex` takes (i)'s two sentences (at
  `def:pencil-d-lift` and `lem:pencil-d-ear-free`) and (ii)'s drafted paragraph ("one
  construction at two dimensions"; `simplify-ii.md`, Step 3(a)); the flat motion count goes, for
  the flat split in every dimension. On §7's nine calls: none is outdated, since the route does
  not change.

## 8. The open (2026-11-12)

From an attended session, which the PI began with "Let's open phase 44 following
@notes/PencilScenes.md." The session agent put four calls to the PI, each with a recommendation.

- **The rename.** The PI chose "baseLiftSpace (Recommended)": the lifts of the base realization
  r⁰. It keeps the chapter's word, so `IsTrivialLift`, `liftMaps` and "lift space" stay, and it
  leaves `sceneSpace` to ORIGAMI's general definition. Companions: `baseLiftSpaceTilde`,
  `mem_baseLiftSpace`, and the lemma names that contain them.
- **The two additions to `pencil-d.tex`** (§7a). The PI chose "Both, in the pencil-d slice
  (Recommended)": the two sentences at `def:pencil-d-lift` and `lem:pencil-d-ear-free`, the
  paragraph in Part C's introduction, each after its derivation is checked in the slice.
- **Docstrings.** The PI chose "Yes, in the rename slice (Recommended)": one Lean slice does the
  rename and the docstring edits, comments only.
- **The flat motion count.** The recommendation was to keep it. The PI asked:

  > "Would it make sense for us to retire it and mention that a generalization of Whiteley 1984
  > 5.1 is formalized, with a pointer to that? "

- **The session agent's answer, from the Lean.** Half of such a generalization is formalized:
  every motion of every configuration over q, at any number of heights, projects to lifting
  planes (`gradePi_comp_mem_liftingPlanes`), and the every-dimension flat rank is a count, proved
  through P_q and padding, not through §5.1. The isomorphism (motions of the flat structure are
  constants ⊕ F(q)) is formalized at d = 3 only. So the sentence would overstate unless one
  lemma is added: at the flat configuration with any number of zero heights, the map to F(q) is
  onto, with kernel the constant screws killed by ⋀²π (the agent's sketch, unchecked).
- **The PI's call.** Offered that lemma, keeping the count, or retiring it with a pointer only,
  the PI chose "Retire, add the every-dimension split (Recommended)": `lem:pencil-flat-split`
  is restated in every dimension and re-pinned, and the d = 3 count (about 120 lines) goes, with
  its use in `MainComponent/Bridge.lean` turned to the padding proof. A read-only spike comes
  first; if the lemma or the import order fails, the count stays.
- **Settled without a question:** one work log, `notes/Phase44.md`, no sub-phases; the slices
  and their order are its checklist. §7's order changes in one place: the spike and the flat
  split come before the flat-rank prose, and the road map stays last before the close.
