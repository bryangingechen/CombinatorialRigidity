# PENCIL-SCENES — the pencil proof against its sources (planning note)

**Status:** queued by the PI on 2026-11-09, ahead of ORIGAMI; unopened, and its number is minted
on open. Same editing discipline as phase notes (≤ 8-line entries, lift cross-cutting lessons).
**Next concrete step:** the read-only recon of §5 (an attribution ledger over the three pencil
chapters, and Q1–Q4), then the open with the PI, who settles the scope (§6). Nothing is
dispatched yet.

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

## 2. What the sources say

Read on 2026-11-09 against the PDFs in `.refs/` (filenames in `REFS.md` *Catalogue of `.refs/`*).
Page numbers are the printed ones. Bib keys are given where `blueprint/src/bibliography.bib` has one.

- **Crapo–Whiteley 1982** (*Structural Topology* 6, 43–82; `crapoWhiteley1982`). §4, Proposition
  4.1 (p. 70) and Corollary 4.2 (p. 71): the motions of a panel polyhedron (panels on faces, hinges on
  edges) match the stresses of its bar skeleton that satisfy a condition round every closed path on
  the surface, automatic for a spherical polyhedron. Example 4.4 (pp. 72–73): for a flat
  tetrahedron, the panel motions are the polyhedra over it, the normal velocity read as height;
  "true in great generality, as we shall see in the sequel". No general statement in this paper.
- **Whiteley 1982**, "Motions and stresses of projected polyhedra" (*Structural Topology* 7,
  13–38; no bib entry). The kinematic proof of Maxwell's theorem. P. 14: "the process of lifting a
  plane picture up to the polyhedral scene in space is an infinitesimal motion of the panel
  structure, composed of panels on the faces and hinges along the edges of the flat projection".
  Proofs of Theorems 3.1 (pp. 18–19) and 3.3 (pp. 20–21) give both directions: each panel rotates
  about the line where its face plane meets the projection plane, and adjacent panels agree along
  their hinge. Stated for abstract oriented polyhedra. §3.4 (p. 23): the path condition is
  automatic for spherical polyhedra, and a 2-connected planar graph has one (Corollary 3.5). §4.4
  (pp. 32–33): K₃,₃ made planar by inserting a crossing as a joint (Bow; Proposition 4.4), not
  possible in general. P. 15 announces the correspondence with plane frameworks (next entry).
- **Whiteley 1984**, "A correspondence between scene analysis and motions of frameworks" (*Discrete
  Appl. Math.* 9, 269–295; no bib entry). Any incidence structure S = (V, F; R) and plane picture
  (Definitions 2.1–2.4: scenes; flat, foldable, sharp; degree of freedom = dim scenes − 3). §4.1
  (p. 282): row-reducing the scene matrix to remove the heights leaves the rigidity matrix of a
  plane plate-and-bar framework L(S(p)), a plate per face and, for each vertex w, a fan of bars on
  the line with coordinates (x_w, y_w, 1) joining the plates of the faces at w. Proposition 4.1
  (pp. 282–283): scenes ≅ motions, the plane of a face = the centre of its plate; Corollary 4.2:
  flat/rigid, foldable/shaky, sharp/completely shaky, equal degrees of freedom. Theorems 4.1
  (p. 285) and 4.9 (p. 287): an inverse map, for pictures and for abstract incidence structures.
- **Whiteley 1984, continued.** §5 (pp. 287–289), how the correspondence was found: the joined
  plate structure (plates in a plane, joints at points) has vertical motions that are affine
  velocity functions agreeing at the joints; adding the joint velocities as heights gives the scene
  equations (§5.3), and a polarity of the plane takes it to the plate-and-bar framework (§5.2).
  §7.2, Remark (p. 292): plane pictures of 4-dimensional scenes with hyperplane faces give
  non-linear equations.
- **Whiteley 1989**, "A matroid on hypergraphs, with applications in scene analysis and geometry"
  (*Discrete Comput. Geom.* 4, 75–95; no bib entry). Theorem 3.1 (p. 83): for any incidence
  structure, incidences are independent in the scene matrix of a generic picture iff
  i′ ≤ v′ + 3f′ − 3 on every nonempty subset; Corollaries 3.2–3.3 (pp. 84–85): Sugihara's
  conjecture, and the dimension of the space of scenes. §5.1 (p. 87): the polar reading (Crapo's
  concurrence geometries, parallel redrawing). Theorem 5.4 (p. 92): a plane identified body-and-joint
  framework has an independent (isostatic) realization iff one with each body's joints collinear,
  iff a count. P. 93: the spatial analogue as a conjecture (each body's hinges in one plane); "the
  methods used here do not extend".
- **Whiteley 1996** §8.3 (`whiteley1996`, the author's preprint pages): liftings of a picture of
  any incidence structure; Remark 8.3.2, polarity about the paraboloid takes liftings on S to
  parallel scenes on the dual structure S* (points and faces swapped). Theorem 5.1.3: Maxwell's
  theorem, for planar graphs.
- **Jackson–Jordán 2008** (`jacksonJordan2008pin`; `.refs/` holds the 2006 EGRES report). Theorem
  7.2(b): a pin-collinear body-and-pin realization of rank 3|V| − 3 − def. Their Theorem 7.4
  re-derives Whiteley 1989 Theorem 5.4, the independent case. A keyword search of the report finds
  no mention of scenes or liftings beyond the titles of their references.

## 3. The pencil proof's pieces against them

The incidence structure throughout is **S_G**: the points are the bodies, the faces are the closed
neighbourhoods N[v], and w lies on face v iff w ∈ N[v]. The incidence is symmetric, so S_G is its
own dual in Whiteley 1996's Remark 8.3.2; the pencil polarity (`sec:pencil-duality`) is this.

| Node or passage | Classical source (§2) | What the chapter says now |
|---|---|---|
| `sec:main-component-carrier` intro, `def:pencil-lifting-space` | Scenes over a picture: Whiteley 1984 Defs 2.1–2.4 | "as in scene analysis"; cites Whiteley 1996 §8.3 |
| `lem:pencil-lifting-planes-dim` (F(q) ≅ L(q)) | Planes fix heights, and heights fix planes: Whiteley 1984 Prop. 4.1's proof; Whiteley 1989 Thm 3.1's proof, (a)⟺(c) | uncited |
| `sec:main-component-flat` intro, `lem:pencil-flat-split`, `thm:pencil-flat-rank` | Flat panel motions = liftings: Whiteley 1982 pp. 14, 18–21; Whiteley 1984 §5.3 | cites Crapo–Whiteley Ex. 4.4 (the tetrahedron) only |
| `lem:pencil-lifting-planes-motions` (liftings = motions of P_q) | Whiteley 1984 Prop. 4.1, each vertex's fan the star from its own plate: adjacent plates get two bars, one pin; P_q is pin-collinear | uncited |
| `sec:main-component-jj`, `thm:pencil-jj-equality` | JJ 2008 Thm 7.2(b); the generic scene dimension of S_G, which Whiteley 1989 Thm 3.1 counts (Q1); Whiteley 1989 Thm 5.4 is the independent case | cites JJ 2008; the scene reading and Whiteley 1989 unsaid |
| `def:pencil-d-configuration` (d − 2 heights) | d − 2 independent scenes over one picture; contrast Whiteley 1984 §7.2's hyperplane faces | unsaid |
| `def:pencil-d-lift` (Part C) | the same construction over a base in P³? (Q2) | unsaid |
| `sec:pencil-roadmap`, the three chapter introductions | the whole of the above | no lineage given |

New, as far as the 2026-07-23 search found (ROADMAP §39): the pencil realization theorem itself,
the reduction (A), the main-component induction's steps and coverage (B), and the lift (C). The
classical part is the carrier: the space of scenes over a picture of S_G, its two descriptions, and
its two framework readings (the flat panel structure, and P_q).

## 4. Observations from the session, not checked against a source

The agent's own derivations on 2026-11-09. Check each before it goes into a chapter.

- **O1.** By `lem:pencil-d-rank-scale-shift`, the rank of a configuration depends only on the
  picture q and W, the span of the heights' classes in L(q)/Aff(q), with dim W ≤ d − 2.
- **O2.** The universal lift v ↦ ev_v ∈ L(q)* is a configuration in P^{2+def₂} (at a main picture)
  whose closed neighbourhoods each span a plane, and every configuration over q is a linear
  projection of it. If d − 2 ≥ def₂, all general configurations over a fixed main picture are
  projectively equivalent.
- **O3.** Writing h_v(ξ) = g_v·ξ + c_v, the face gradients satisfy (g_u − g_v)·(q_u − q_v) = 0:
  g is an infinitesimal motion of the bar framework (G, q), the trace of Maxwell's reciprocal
  figure. Not onto: the rotation fails, by twice each cycle's signed area. Compare Whiteley 1984
  §5.4.
- **O4.** The hinges are affine in the heights only at d = 3 (`notes/pencil/workbook/K-main.md`,
  MC-3); for d ≥ 4 two heights give quadratic Plücker coordinates.
- **O5.** Why planarity never enters: the face-adjacency graph of S_G is G itself, so a scene is
  a potential on G, that is, a motion of a framework on G. Classical Maxwell turns potentials on
  G* into stresses on G by planar duality, which is where Whiteley 1982's path condition comes in.

## 5. The recon (proposed, not dispatched)

Read-only. Deliverable: an **attribution ledger** with one row for each node or prose passage of
`pencil.tex`, `main-component.tex` and `pencil-d.tex` that states or uses the material of §3 (the
scene space, its two descriptions, the flat motions, P_q, JJ's equality, the polarity, the d − 2
heights). Each row gives the label, what it claims, the source and page that has it (checked
against `.refs/`, not this note), and its status now: cited, partly cited, uncited, or presented as
new. It also answers:

- **Q1.** Does Whiteley 1989 Theorem 3.1's count, evaluated on S_G, give dim L(q) = 3 + def₂(G)
  at a generic picture, a second derivation of JJ's equality? Over every infinite field? Whiteley's
  generic is algebraically independent over ℚ; the project derives the equality from KT Theorem 5.6
  at d = 2.
- **Q2.** Is Part C's lift a space of scenes in Whiteley's sense, over a base in P³ whose faces are
  planes? Whiteley 1984 §7 treats K-space pictures with hyperplane faces only.
- **Q3.** The pencil stratum's own lineage. Re-run 2026-07-23's search (no result found) with the
  new leads: Whiteley 1989's p. 93 conjecture, Tay–Whiteley 1984 (`tayWhiteley1984`), and Whiteley
  1999 and 2005 (in `.refs/`).
- **Q4.** Sources cited by these papers but not in `.refs/`: Crapo–Whiteley's preprints on plane
  stresses and projected polyhedra, Sugihara (1980s papers and book), Huffman 1977, and Whiteley's
  "Lashed and woven rods". Which would a chapter cite?

## 6. Scope at the open (the PI's call)

- **(a) Exposition.** Chapter prose and citations only: the road map and the three introductions
  say what is classical (§2) and what is new; each node of §3 cites its source; no statement or
  Lean change. A citation-only first slice is ready: Whiteley 1982 and 1984 into the bibliography,
  cited at `sec:main-component-flat` and at `lem:pencil-lifting-planes-motions`.
- **(b) The proof.** State the classical part in its general form (scenes over a picture of any
  incidence structure ≅ motions of the reduced plate framework, Whiteley 1984 Proposition 4.1) and
  derive the chapter's lemmas as its case S_G. This may touch the Lean.
- **(c) The observations.** Whether O1–O5 go into the chapters; the road map's "Four observations"
  paragraph is the natural home for O1 and O5.
