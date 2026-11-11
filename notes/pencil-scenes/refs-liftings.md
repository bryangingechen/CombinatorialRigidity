# PENCIL-SCENES recon: the liftings, scene-analysis and Maxwell references added on 2026-11-10

*Delivered by a read-only recon agent on 2026-11-11. Nothing in the tree was changed except this
file. Read `notes/PencilScenes.md` §2–§4 first; this report answers that note's questions about
ten PDFs the earlier recon never read.*

**Scope.** Crapo–Whiteley 1993 and 1994, Sugihara 1983, 1984 and 1986, Maxwell 1864 and 1870,
Rybnikov 1999, Huffman 1977 and Mackworth 1973, all from `.refs/`. **Questions:** (1) which rows of
`notes/PencilScenes.md` §3 each source bears on and what to cite there; (2) whether it moves
anything from "new" to "classical" or contradicts O1–O7, especially O3; (3) bibliographic data
verified on the PDF.

**Method.** The text layers were read with pypdf (`REFS.md` *Reading PDFs*). CW93 is a scan with an
uneven OCR layer, so I read its key pages as page images: pdf pp. 1–2, 14–24 and the cropped
margins of pp. 1, 2, 12, 13, 23 and 24. I read Sugihara 1984 p. 85 as an image to get eq. (10)
exactly. Page numbers are printed ones unless marked "pdf". Sugihara 1986 is the 2006 re-typeset web
release, so it is cited by section, theorem or equation number only. **Verified** means read on the
page. **Inferred** marks my own derivations. One claim was checked by computation (O3 at θ(2,2,3),
Appendix).

**Notation** as in the note: S_G has the bodies as points and the closed neighbourhoods N[v] as
faces; q is the picture; h_v(ξ) = g_v·ξ + c_v is the plane of face v; L(q) and F(q) are the height
and plane descriptions (`def:pencil-lifting-space`, `def:pencil-lifting-planes`).

---

## Verdict in brief

- **CW93 runs 55–78.** The scan does carry page numbers, cut off at the outer margin. The visible
  digits fit pdf page = p. − 54 throughout, and the article ends on p. 78 with a complete
  bibliography. CW94's own reference list (p. 280) gives 55–78, and Rybnikov's (ref. 12) gives
  55–78 too, though it misprints the volume as 19. `REFS.md`'s remark that the pages "carry no
  journal page numbers" is wrong. The coordinator should fix it; I did not touch `REFS.md`.
- **Nothing moves from new to classical.** No source in this cluster has hinges, several heights,
  or anything like the pencil stratum.
- **O3 is classical in mechanism and new only as a statement about S_G.** The perpendicularity
  (g_u − g_v)·(q_u − q_v) = 0 is the gradient-space rule (Maxwell 1870, Huffman, Mackworth,
  Sugihara 1986 §11.1, CW93 Thm 4.5(a), CW94 Prop. 4.1). Reading a face diagram as a parallel
  drawing, and so as an infinitesimal motion, is CW94 Remarks 2.8 and 3.2. O3's failure to be onto
  has a precedent in CW94 p. 277. Two things are S_G-specific: the face diagram lives on G itself,
  not on a dual graph, and the cycle condition is not automatic. No source contradicts O3. Its
  phrase "where Maxwell–Cremona has a stress" is correct once the planar-duality step is named
  (§2 below).
- **The carrier gains a co-originator.** Sugihara 1984 §§2.2 and 3.1 states the scene equations for
  an arbitrary incidence structure, the linear space of their solutions and its dimension. Its
  p. 84 also states the equality of the vertex and face descriptions (`lem:pencil-lifting-planes-dim`).
  The paper was received in 1980, and Whiteley 1984 (same journal volume) cites its technical
  report. Cite it beside W84 Defs 2.1–2.4.
- **Attribution fix at W89 Thm 3.1.** Sugihara's conjecture is the sharp-lift count
  i′ ≤ v′ + 3f′ − 4 on two or more faces (Sugihara 1984, Conjecture 2, p. 92). W89 Thm 3.1's
  independence count i′ ≤ v′ + 3f′ − 3 is W89's own extension (W89 p. 76). The note's §2 and §5
  attach "Sugihara's conjecture" to the independence count; that should be adjusted.

---

## 1. Crapo–Whiteley 1993 (CW93), "Plane self stresses and projected polyhedra I"

**Read.** pp. 55–59 and 60–64 (OCR), and pp. 68–78 (page images), which cover §3, §4 and the
bibliography. pdf page = p. − 54.

**Page range (Q3).** The outer margins carry page numbers that the scan crops. Visible: pdf 1
"5…", pdf 2 "…6" (reads 56), pdf 12 "…6", pdf 13 "6…", pdf 23 "7…", pdf 24 "…8". That is
consistent with 55, 56, 66, 67, 77, 78. pdf 24 (p. 78) holds the whole bibliography, [1]–[29], with
the top half of the page blank, so the article ends on p. 78. Independent confirmations: CW94's
reference [1] (p. 280) reads "Structural Topology 20 (1993), 55-78", and Rybnikov's ref. 12 gives
55–78 (volume misprinted as 19). **Settled: 55–78.** The 55–79 in the repository record and Zbl
presumably counts a blank verso; I could not check that.

**Content verified on the page.**
- p. 56: for 3-connected planar drawings, a self stress exists iff a reciprocal exists iff a spatial
  polyhedron does. "To check a polyhedral projection Maxwell and Huffman used a 'dual diagram'
  formed by the gradients of the faces of the spatial polyhedron, taken as plane points — again
  Maxwell's reciprocal."
- p. 57: the refinements for general oriented polyhedra. A self stress gives a reciprocal iff the
  vector sum vanishes across every face-edge cycle. It gives a spatial polyhedron iff both the
  vector sum and the moment sum vanish. "All these conditions are trivially true for the self
  stresses on any planar graph." A second paper is promised, with "the full vector space of
  reciprocals and spatial liftings".
- p. 58: "The theory presented here has a polar form which is presented in [28]. In that setting, a
  projective section of a spatial polyhedron (the spatial polar of a projection) is paired with a
  projection…". Analogues for oriented 4-polytopes are deferred to a third paper.
- pp. 58–59: the gradient space "has been recognized as a necessary condition for the lifting of a
  polyhedral picture, and sometimes accepted, without proof, as a sufficient condition."
- p. 63, Def. 2.5: combinatorial oriented polyhedra (2-manifolds), "explicitly self-dual".
- p. 68, Def. 3.1 (reciprocal framework) and **Thm 3.2 (Maxwell)**: a framework on a 2-connected,
  edge-3-connected planar graph has a full self stress iff it has a reciprocal.
- p. 70, **Cor. 3.5**: for any oriented polyhedron, a full stress with Σω_e v_e = 0 on face-edge
  cycles is equivalent to a reciprocal.
- p. 71: Example 3.6 (a torus violates the cycle condition), and Thm 3.6 (Bow's crossing joints).
- p. 72, **Def. 4.2, the face diagram**: P^j = (A^j, B^j, 0) for the face plane
  A^j x + B^j y + z + C^j = 0. These points are "the negatives of the gradients of the face planes,
  treated as functions of x and y".
- p. 73, Def. 4.3 (the Maxwell polarity L(x, y, z) = (x, y, 1, z)) and Def. 4.4 (titled
  "Proposition 4.4" in the French column): it preserves incidences, about the paraboloid
  x² + y² + 2z = 0.
- p. 74, **Thm 4.5(a)**: the vertex diagram and the face diagram of any polyhedral surface are
  reciprocal frameworks. Fig. 13's caption: "For a spatial edge we have the projection
  perpendicular to the line of the gradients."
- p. 75, **Thm 4.6**: the moment condition Σω_e m_e = 0 on face-edge cycles is equivalent to a
  polyhedral surface with the given reciprocal pair. In the proof (p. 76) the heights are
  integrated along paths, and they are well defined iff the moment sums vanish on cycles.
- p. 77, Cor. 4.11: "essentially the original theorem of Maxwell [1864]". Its lead-in cites a
  "Theorem 2.5", but no theorem of that number exists (Def. 2.5 and Prop. 2.4, cut sets, p. 61, do).
- **Reference numbering.** The text's reference numbers are off by one from the printed
  bibliography in places. For example, "Maxwell [17]" is bibliography [18] and "Mackworth and
  Huffman [16,13]" is [17, 14]. "[28]" (p. 58) must be [29], Whiteley 1991, "Weavings, sections and
  projections of spherical polyhedra" (*Discrete Appl. Math.* 33 per CW93; CW94 ref. [14] says 32).
  "Whiteley [26]" in Remark 4.8 is therefore ambiguous between W82 and Whiteley 1985.

**Rows (Q1).** CW93 has no general incidence structures (it works with oriented 2-manifolds), no
several heights and no hinges. It bears on O3 and O5 and on the road map's history:
- Maxwell's theorem with cycle conditions: Thm 3.2, Cor. 3.5, Thm 4.6, Cor. 4.11, and the summary
  on p. 57.
- The face diagram as reciprocal: Def. 4.2 and Thm 4.5(a).
- The Maxwell polarity: Def. 4.3–4.4.

**Q2.** Nothing new becomes classical, and O1–O7 are not contradicted. For O3 see §2.

**Bib (Q3).** H. Crapo, W. Whiteley, "Plane self stresses and projected polyhedra I: The basic
pattern" / "Autocontraintes planes et polyèdres projetés I : le motif de base", *Structural
Topology* 20 (1993) 55–78. Bilingual; French translation by Jean-Luc Raymond. No DOI.

## 2. O3 against CW93, CW94 and the gradient-space sources (the main question)

O3: face gradients satisfy (g_u − g_v)·(q_u − q_v) = 0, "an infinitesimal motion of the bar
framework (G, q), where Maxwell–Cremona has a stress. Not onto: the rotation fails".

- **The bar condition is the classical gradient-space rule.** When two face planes meet, the
  picture of their intersection line is perpendicular to the difference of their gradients. Sources:
  - Maxwell 1870 pp. 7–8, the origin: "Each of these lines is perpendicular to the projection of
    the other".
  - Huffman 1977 p. 479 and Mackworth 1973 p. 125, its rediscovery in scene analysis.
  - Sugihara 1986 §11.1, eq. (11.2) and Thm 11.1, the presentation.
  - CW93 Thm 4.5(a), p. 74, and CW94 Prop. 4.1, p. 272, the modern statement.

  For S_G, faces u and v share the points q_u and q_v, so the rule gives O3's condition. The rule
  is stated for any two planes, so nothing about polyhedra is needed.
- **Reading the gradients as a motion is classical too.** In CW94, the face diagram of a lifting is
  a reciprocal (Prop. 4.1). The reciprocals of a 2-frame are exactly the parallel drawings of its
  trivial reciprocal (Remark 3.2, p. 269). Parallel drawings become infinitesimal motions on
  turning by 90°, with translations going to translations and dilations to rotations
  (Remark 2.8, p. 266).
- **What is specific to S_G.** For a polyhedron, the face diagram is a 2-frame on the *dual* graph,
  and planar duality converts it into a stress of the primal (G, q): CW94 Thm 3.1 and Cor. 3.2
  (pp. 269–270), CW93 Thm 3.2. That is the precise content of "where Maxwell–Cremona has a stress".
  The faces of S_G adjoin along G's own edges (O5). So the face diagram is a 2-frame on G whose
  edges are perpendicular to G's own edges, which makes it a motion of (G, q) itself. No source in
  this cluster states this for S_G or for any non-polyhedral incidence structure.
- **The failure to be onto has a precedent.** CW94 p. 277: "a parallel drawing in 3-space always
  projects to a parallel drawing of the projection. However the converse is false". The paper
  proves that the projection is onto for spherical polyhedra (Thm 5.1(ii), p. 277, and Cor. 5.2,
  p. 278), promises a toroidal failure, and gives a skew quadrilateral as an example
  (Example 5.4). O3's obstruction is a sum over the cycles of G. Its role matches CW93's moment
  condition (Thm 4.6(i), p. 75), which planarity makes automatic (p. 57) and S_G does not.
  *Inferred:* the analogy is mine; no source draws it.
- **How the two fit together (inferred, checked algebraically, not in any source for S_G).** CW94
  Remark 5.8 (p. 280), crediting W89, says that "for any configuration of planes and points polarity
  takes the space of parallel drawings of one configuration to the space of 'shadow equivalent'
  configurations of its spatial polar". Apply the Maxwell polarity (CW94 Def. 4.3) to a scene of
  S_G:
  - Face v becomes the point (A_v, B_v, C_v), which projects to −g_v.
  - Point w becomes a plane with the fixed normal (x_w, y_w, 1).
  - For each edge uv, the two polar points lie on the line where the planes of u and v meet, and
    that line projects perpendicular to q_u − q_v.

  So O3's gradient map is CW94 §5's projection of 3-space parallel drawings, applied to the polar
  of S_G, which is again S_G (the incidence is symmetric), and its failure to be onto is the
  "converse is false" of p. 277.
- **Computation.** At θ(2,2,3), with the note's picture, an exact computation of my own finds:
  dim F(q) = 4; the gradient image has rank 3 (= dim F(q) − 1, so the map is injective modulo the
  global constant); every gradient vector is a motion; the image contains both translations; adding
  the rotation raises the rank to 4; the motions of (G, q) have dimension 5. This agrees with O3
  and the note. Script in the Appendix.

**Proposed wording for O3** (if it goes into a chapter, §6(c)): "the face diagram of a scene
(Maxwell 1870; CW93 Def. 4.2) is a 2-frame on G perpendicular to (G, q), so the gradients form an
infinitesimal motion of (G, q) (CW94 Remarks 2.8, 3.2). For a spherical polyhedron the face
diagram lives on the dual graph and corresponds to a stress (CW94 Thm 3.1). Not every motion
lifts, as in CW94 p. 277."

## 3. Crapo–Whiteley 1994 (CW94), "Spaces of stresses, projections and parallel drawings for spherical polyhedra"

**Read.** All of pp. 259–281. pdf page = p. − 258. Text layer with bitmap fonts: ligatures are lost
and spurious slashes appear.

**Content verified on the page.**
- p. 259 (abstract): isomorphisms among (a) the affine space of polyhedra with a fixed projection,
  (b) the self stresses and (c) the reciprocals with one fixed vertex. Dually, maps among (d) the
  parallel drawings of spatial polyhedral surfaces, (e) the frameworks with a fixed reciprocal and
  (f) "the space of parallel drawings (infinitesimal motions) of the projections".
- p. 261: "Our paper [14] presents a new projective form of the reciprocal – as the cross-section of
  the spatial polyhedron". [14] is Whiteley's "Weavings, sections and projections…". The toroidal
  sequel [2] and the 4-polytope paper [3] are preprints.
- p. 263, Remark 2.3: the class is closed under combinatorial duality. pp. 265–266: 2-frames
  (Def. 2.5), stresses (Def. 2.6), the cycle conditions (Prop. 2.1), parallel drawings (Def. 2.7)
  and **Remark 2.8**.
- p. 268, Cor. 2.2: |E| − dim stresses = 2|V| − dim parallel drawings.
- p. 269, Thm 3.1 and Remark 3.2. p. 270, Cor. 3.2 and Cor. 3.3: dim stresses(H) − dim stresses(H*)
  = |F| − |V|.
- p. 272, Def. 4.2 (the face diagram, P_j = (A_j, B_j)) and **Prop. 4.1**: the vertical projection
  and the face diagram are reciprocal.
- p. 273: Def. 4.3 and Remark 4.4 (the Maxwell polarity, about x² + y² + 2z = 0) and Prop. 4.2.
- p. 274: Thm 4.3, and Def. 4.5: the vertical liftings form an affine space, a vector space once one
  face is fixed.
- p. 275, **Thm 4.4**: stresses ≅ reciprocals with P_0 = 0 ≅ parallel drawings of a reciprocal ≅
  liftings with Q_0 fixed.
- p. 277, **Thm 5.1** (shadow-equivalent surfaces ≅ stresses; parallel drawings of the surface ≅
  parallel drawings of the projection), the "converse is false" passage and Example 5.4. p. 278,
  Cor. 5.2.
- pp. 279–280, **Remark 5.7**: dimensions are projectively invariant, and "lifting to a spatial
  polyhedron, doing a projective transformation in 3-space (no face vertical) and reprojecting will
  not change the dimension". p. 280, **Remark 5.8** (above).

**Rows (Q1).**
- The road map's history: the statement that liftings ≅ stresses for planar graphs is Thm 4.4, as
  the earlier recon said.
- O3: §2 above.
- `lem:pencil-d-rank-collineation` (optional): Remark 5.7 is a projective-invariance statement for
  lifting spaces, not for hinge-framework ranks. CW82 §3.6 stays the citation.
- O6 and `sec:pencil-duality`: Def. 4.3 and Remark 4.4 give the Maxwell polarity. This is not the
  chapter's convention. The chapter takes b_v = (x_v, y_v, z_v, 1) as a panel normal, so the
  panel's trace on z = 0 is fixed and the height tilts the panel about it (O6, O7). Under Maxwell's
  polarity the height translates a plane of fixed normal (x_v, y_v, 1). *Inferred:* the two
  conventions differ by the collineation that swaps the third and fourth homogeneous coordinates.
  The "cross-section" form that p. 261 attributes to [14] looks like O6's reading. [14] is unread
  and not in `.refs/` (open lead).

**Q2.** Nothing moves from new to classical, and O1–O7 are not contradicted. O3 is refined (§2).

**Bib (Q3).** H. Crapo, W. Whiteley, "Spaces of stresses, projections and parallel drawings for
spherical polyhedra", *Beiträge zur Algebra und Geometrie / Contributions to Algebra and Geometry*
35 (1994), No. 2, 259–281, Heldermann Verlag, Berlin. Received August 2, 1993. The code line
"0138-4821/93" gives the ISSN. The last printed page is 281, so Karpenkov et al.'s 259–282 is off by
one.

## 4. Sugihara 1984, "An algebraic and combinatorial approach to the analysis of line drawings of polyhedra"

**Read.** All of pp. 77–104. pdf page = p. − 76. p. 85 was also read as an image.

**Content verified on the page.**
- p. 79: an incidence structure (V, F, R), R ⊆ V × F, with face planes a_j x + b_j y + z + c_j = 0.
  The paper's history of the reciprocal figure: Maxwell and Cremona, then Huffman and Whiteley, then
  Mackworth and Kanade for categorizing lines.
- p. 80, **eq. (1)**: a_j x_i + b_j y_i + z_i + c_j = 0, "a linear equation with respect to unknowns
  z_i, a_j, b_j, and c_j". (2) collects them as Aw = 0, "the system of fundamental equations".
- p. 83: the solutions "form an (n + 3m − rank(A(R)))-dimensional linear space".
- p. 84: σ_D(V) = τ_D(F) = n + 3m − ρ_D(R), "since we can specify a polyhedron uniquely either by
  fixing the z-coordinates of some of its vertices or by fixing some of its surfaces". This is the
  vertex and face descriptions having equal dimension, for correct pictures.
- p. 85, Thm 2 and **eq. (10)**: the transformation (x, y, z) ↦ (x, y, αx + βy + γz + δ), γ > 0,
  preserves the picture and takes polyhedra to polyhedra, so σ_D(V) ≥ 4.
- **§3.1, pp. 85–86**: "The system of fundamental equations (2) depends on the incidence relations
  between vertices and faces, but does not depend on properties of edges. Therefore, while (2) is
  originally defined for a picture of a polyhedron, we can consider it as the system of equations
  associated with a picture of a three-dimensional configuration composed of planar surfaces
  (extended infinitely) and points on them." Then a general incidence structure: each vertex on at
  least one face, each face with at least three vertices. A realization is a solution of (2). "(2)
  has a trivial solution in which every surface is identical." "The realizations of (2) form a
  linear space. The dimension of this space, n + 3m − rank(A), is called the degree of freedom of
  (2)" (p. 86).
- p. 87: rotors, and μ_S(X) = |V(X)| + 3|X| − |R(X)| − 4 (eq. (11)). Theorems 3–5.
- p. 90, Lemma 3: if S is generically independent, its degree of freedom is |V| + 3|F| − |R|.
- p. 92: **Theorem 6** (without rotors, position-free iff μ-nonnegative) and **Conjectures 1–2**
  (position-free implies generically independent; position-free iff μ-nonnegative). p. 93: Cors.
  6.1 and 6.2 settle convex and trihedral polyhedra, and 3-connected planar graphs.
- The dates: received 15 April 1980, revised 27 August 1981 and 15 September 1983.

**Rows (Q1).**
- `def:pencil-lifting-space` and `sec:main-component-carrier`: **cite §2.2, eqs. (1)–(2)
  (pp. 79–80), and §3.1 (pp. 85–86)** for the scene equations of an arbitrary incidence structure,
  the linear space of their solutions and its dimension. The sentence "trivial liftings, which put
  all the faces in one plane" corresponds to the trivial solution on p. 86 (all surfaces identical).
- `lem:pencil-lifting-planes-dim`: p. 84 states the equality of dimensions in general. Caveat: its
  justification, like Sugihara 1986's eq. (5.6), tacitly needs each face's points not to lie on one
  line. The chapter's admissibility hypothesis supplies that.
- `lem:pencil-d-condition-linear`: p. 80, eq. (1), beside W89 p. 78. It is earlier, and the paper
  was received in 1980.
- `lem:pencil-d-rank-scale-shift` (d = 3): eq. (10), p. 85, is the scene-level fact that
  z ↦ γz + (affine) preserves the picture and maps scenes to scenes. Rank invariance stays CW82 §3.6.
- `thm:pencil-jj-equality` (the Q1 route): **Conjecture 2, p. 92** is "Sugihara's conjecture".
  W89 p. 76 quotes it as "lifts to a sharp polyhedral scene iff i′ ≤ v′ + 3f′ − 4" and says
  Sugihara proved it for 3-connected spherical polyhedra (Cor. 6.2). **Precision:** the independence
  count i′ ≤ v′ + 3f′ − 3 of W89 Thm 3.1, which Q1 uses, is W89's extension ("We verify the full
  conjecture, and the extension", W89 p. 76). Sugihara 1986 §6.2 likewise credits only Thm 6.2 and
  Cor. 6.2.1 to Sugihara's conjecture. Suggested wording: "Whiteley 1989 Thm 3.1, which settles
  Sugihara's conjecture (Sugihara 1984, Conjecture 2)".

**Q2.** The carrier was already classical. This adds Sugihara as co-originator of its equations and
dimension count, and nothing moves. O5's "planarity never enters" matches §3.1's "does not depend
on properties of edges". No contradiction.

**Bib (Q3).** K. Sugihara, "An algebraic and combinatorial approach to the analysis of line drawings
of polyhedra", *Discrete Appl. Math.* 9 (1984) 77–104, North-Holland. The DOI
10.1016/0166-218X(84)90092-1 is not printed on the PDF; it comes from the earlier recon's Crossref
check.

## 5. Sugihara 1983, "A unifying approach to descriptive geometry and mechanisms"

**Read.** All of pp. 313–328. pdf page = p. − 312.

**Content.**
- pp. 313–314: the scene equations again, linear in z_i, a_j, b_j, c_j (p. 314). The point of the
  paper is that the submodular functions of line drawings and of plane rod frameworks "have the same
  mathematical properties" (p. 313).
- p. 315, Thm 1: for convex or trihedral polyhedra, regular iff μ_S ≥ 0. pp. 316–317: Laman's
  theorem.
- **Remark 1, pp. 317–318**: the other representation of a plane rod structure. Rods are the
  objects, each with three degrees of freedom, and a joint of k rods imposes 2(k − 1) constraints.
  (Q, σ′) is "a 3-matroid".
- **Table 2, p. 320**, "Summary of similarity": the faces F of a line drawing (a 3-matroid) pair
  with the rods Q (a 3-matroid). The minimum rank is 4 for drawings and 3 for rod structures.
- §4 compares principal partitions. Nowhere does the paper give an isomorphism between scenes and
  motions.

**Rows (Q1).** `lem:pencil-lifting-planes-motions` (P_q): optional history only. Sugihara's pairing
of a drawing's faces with the rods of a plane rod-and-joint structure foreshadows P_q, whose bodies
are S_G's faces and are rods along the lines with normals (x_v, y_v, 1). But it is an analogy of
polymatroids, not a correspondence of spaces. W84 p. 269 credits Sugihara 1983 with "a unified
approach", and W84 Prop. 4.1 remains the citation for the isomorphism.

**Q2.** Nothing moves.

**Bib (Q3).** K. Sugihara, "A unifying approach to descriptive geometry and mechanisms", *Discrete
Appl. Math.* 5 (1983) 313–328, North-Holland. Received 23 July 1980, revised 24 November 1980 and
4 December 1981. The DOI 10.1016/0166-218X(83)90004-5 is from the earlier recon, not the PDF.

## 6. Sugihara 1986, *Machine Interpretation of Line Drawings* (cite by section)

**Read.** §1.3, §3.4, §5.1, §6.2, §6.4 (theorem statements), §11.1–§11.4. The web release says the
text is unchanged "except for the corrections of a few of typos".

**Content.**
- §1.3: Falk (1972) and Duda–Hart (1973) were the first to point out the linear equations. Huffman
  (1971) and Mackworth (1973) rediscovered Maxwell's reciprocal.
- §3.4: eq. (3.1), and (3.2) Aw = 0, "linear with respect to the unknowns". Thm 3.1.
- §5.1: Thm 5.1 (degrees of freedom), and **eq. (5.6)**, ρ_V(V) = ρ_H(H_F) = ρ_H(H) = n + 3m −
  rank(A), justified by "every vertex is at least on one face and every face has at least three
  vertices" (the same caveat as above). **Remark 5.1**: (5.1) "essentially represents the
  configuration composed of planar surfaces and points on them".
- §6.2: Thm 6.1 (the independence count, with +3), Thm 6.2 and Cor. 6.2.1. "Theorem 6.2 and
  Corollary 6.2.1 were first conjectured by Sugihara … proved completely by Whiteley (1988)." §6.4:
  Thm 6.3.
- §11.1: eq. (11.2) ("the image of the line of intersection is perpendicular to the vector
  (a1 − a2, b1 − b2)") and Thm 11.1 (the vertex-edge and face-edge diagrams are reciprocal,
  "Maxwell, 1864, 1870; see also Mackworth, 1973").
- §11.3: Thm 11.3 (Maxwell, proved by turning the face-edge diagram through π/2). It ends: "A quite
  different type of a correspondence between line drawings of polyhedrons and rigidity of
  structures is also studied by Whiteley (1984b) (see also Crapo and Whiteley, 1982)."
- §11.4: the generic correspondence for spherical polyhedra with four degrees of freedom (Thm 11.4,
  Cor. 11.4.1–2).

**Rows (Q1).**
- The carrier: §3.4 and §5.1, as the presentation followed, beside Sugihara 1984 and W84.
- `lem:pencil-lifting-planes-dim`: eq. (5.6), with the caveat.
- The JJ equality: §6.2.
- O3: §11.1.
- The road map's history: §1.3 and §11.3.

**Q2.** Nothing moves, and nothing is contradicted.

**Bib (Q3).** K. Sugihara, *Machine Interpretation of Line Drawings*, The MIT Press, Cambridge, MA,
and London, 1986 (© 1986 MIT; preface dated March 1986; MIT Press Series in Artificial Intelligence,
per the 2006 web preface). The `.refs/` copy is the 2006 web re-typesetting.

## 7. Maxwell 1864, "On reciprocal figures and diagrams of forces"

**Read.** All of pp. 250–261. pdf page = p. − 249.

**Content.**
- p. 251: the definition of reciprocal plane figures (corresponding lines parallel, or at right
  angles after turning one figure).
- p. 252: the counts e = s + f − 2 and the determinacy conditions.
- pp. 255–258: the reciprocal of a figure exists exactly under the conditions for it to be a
  perspective projection of a plane-sided polyhedron. p. 258: "Hence the conditions of the
  possibility of reciprocity in plane figures are the same as those of each figure being the
  perspective projection of a plane-sided polyhedron."
- p. 258, "Application to Statics": the reciprocal as a diagram of forces.
- pp. 260–261: reciprocal figures in three dimensions.

There are no heights, gradients or general incidence structures.

**Rows (Q1).** The road map's history only: the origin of the reciprocal ↔ projected-polyhedron
correspondence. CW93 calls Cor. 4.11 "essentially the original theorem of Maxwell [1864]".

**Bib (Q3).** J. Clerk Maxwell, "On reciprocal figures and diagrams of forces", *Phil. Mag.* (4) 27,
No. 182 (April 1864) 250–261, item XLV. The footer on p. 257 reads "Phil. Mag. S. 4. Vol. 27. No.
182. April 1864." It needs a new key; `maxwell1864` is the stiffness paper.

## 8. Maxwell 1870, "On reciprocal figures, frames, and diagrams of forces"

**Read.** pp. 1–15, plus a keyword pass through p. 40. pdf page = p. + 1.

**Content.**
- p. 4: plane reciprocal figures, with corresponding lines at right angles.
- **pp. 7–8: the lifting construction.** The plane z = Ax + By + C goes to the point (cA, cB, −C).
  The line of the reciprocal corresponding to an edge is perpendicular to the edge's projection.
  The points and planes "are reciprocally polar in the ordinary sense with respect to the paraboloid
  of revolution 2cz = x² + y²". Hence "a construction for reciprocal diagrams by considering each as
  a plane projection of a plane-sided polyhedron".
- pp. 10–13: degree-of-freedom counts for frames. p. 13: the theorem that turns a system of forces
  through a right angle.

**Rows (Q1).** O3 (the gradient perpendicularity, at its origin). If O6 is written up, the Maxwell
polarity's origin. The road map's history.

**Bib (Q3).** J. Clerk Maxwell, "I.—On reciprocal figures, frames, and diagrams of forces", *Trans.
Roy. Soc. Edinburgh* 26 (1870) 1–40, Plates I–III. Received 17 Dec. 1869, read 7 Feb. 1870. The DOI
10.1017/S0080456800026351 is printed on the Cambridge cover sheet.

## 9. Rybnikov 1999, "Stresses and liftings of cell-complexes"

**Read.** pp. 481–493 and 504–506, with a keyword pass through the rest. pdf page = p. − 480.

**Content.**
- pp. 481–482: for a PL-realization of a homology d-manifold in R^d with H_1(M; Z_2) = 0,
  d-stresses ≅ liftings ≅ reciprocals. "For the first time this equivalence is proved under the
  general condition H_1(M^d, Z_2) = 0 for d > 3."
- pp. 488–489, §5: liftings, the C^0_1-cofactors and **Thm 5.1** (Stress_d ≅ Lift).
- p. 491: "the space of lifting is always a subspace of the space of stress, the converse is not
  necessarily true", with a torus as the example (Fig. 3).
- p. 493, Thm 6.1: Lift ≅ Rec.
- **§10, p. 504**: "A polyhedral incidence structure is a triple S = (V, F, I) … A polyhedral
  d-picture is a pair (S, p) … A lifting is a pair of 'lifting' maps … Liftings of (S, p) form a
  linear space Lift(S, p). A lifting is sharp if any two affine functions corresponding to faces with
  at least d common vertices are distinct." Also on p. 504: "parallel drawings in R^d are equivalent
  to liftings from R^d to R^{d+1} (see [50])", where [50] is W96.
- p. 505: Sugihara's algorithm "can be modified" to find dim Lift(S, p) for any generic picture.
  This is an unproved aside.

Every lifting here is by **one height**.

**Rows (Q1).**
- `def:pencil-d-lift` (Part C), optional: §10, p. 504 is a published restatement of W84 Def. 7.2
  for K = d, with the same face-hyperplane slack.
- O5: the places where topology enters Maxwell are Thm 5.1's H_1 hypothesis and the inclusion on
  p. 491.
- The road map: the higher-dimensional manifold version, for one height.

**Q2.** Nothing moves; there are no several heights and no hinges.

**Bib (Q3).** K. Rybnikov, "Stresses and liftings of cell-complexes", *Discrete Comput. Geom.* 21
(1999) 481–517, Springer-Verlag New York. Issue 4 and the DOI 10.1007/PL00009434 come from the
earlier recon's Crossref check; they are not printed.

## 10. Huffman 1977 and Mackworth 1973 (history, lowest priority)

- **Huffman 1977** (volume pdf pp. 479–496, pdf page = p. + 4).
  - p. 475: a "completely symmetric" scene/dual-scene duality.
  - p. 476: "The entity dual to the plane z = ax + by + c in the scene is defined to be the point at
    u = a, v = b, w = −c".
  - p. 479: "the direction taken by the line in the picture is orthogonal to the direction taken by
    the corresponding line in the dual-picture".
  - p. 492: the dual surface w = ux + vy − z. *Inferred:* this is Maxwell's paraboloid polarity
    with c = 1.
  - The references are only Huffman 1971 and Hilbert–Cohn-Vossen, so Maxwell is not cited.
  - Bib: D. A. Huffman, "A duality concept for the analysis of polyhedral scenes", ch. 23 in
    E. W. Elcock, D. Michie (eds.), *Machine Intelligence 8: Machine Representations of Knowledge*,
    Ellis Horwood, Chichester; Halsted Press (John Wiley), New York; 1977, pp. 475–492. The
    imprint page (volume pdf p. 8) gives "First published in 1977" and ISBN 85312-058-7 (Ellis
    Horwood).
- **Mackworth 1973** (pdf page = p. − 120).
  - p. 122: dual space.
  - p. 124: "the gradient space G".
  - **p. 125**: for an edge joining surfaces A and B, the line joining G_A and G_B "is perpendicular
    to the picture line if the gradient space is superimposed on the picture".
  - Maxwell is not cited.
  - Bib: A. K. Mackworth, "Interpreting pictures of polyhedral scenes", *Artificial Intelligence*
    4 (1973) 121–137, North-Holland. Received 14 June 1973.
- **Rows.** Only the road map's history, and O3's first clause as the rediscovery in scene
  analysis.

---

## Table: §3 row → proposed citation change (this cluster only)

| §3 row | Proposed change |
|---|---|
| `sec:main-component-carrier`, `def:pencil-lifting-space` | Add Sugihara 1984 §2.2 eqs. (1)–(2), pp. 79–80, and §3.1, pp. 85–86 (any incidence structure; linear space; degree of freedom n + 3m − rank A; trivial solution p. 86). Presentation: Sugihara 1986 §3.4 and §5.1 (Remark 5.1). Keep W84 Defs 2.1–2.4. Optional: Rybnikov 1999 §10, p. 504. History: Falk 1972 and Duda–Hart 1973, per Sugihara 1986 §1.3 (unread). |
| `lem:pencil-lifting-planes-dim` | Add Sugihara 1984 p. 84 and Sugihara 1986 §5.1 eq. (5.6) beside W84 Prop. 4.1. Say that their justification needs non-collinear face points (admissibility). |
| `lem:pencil-flat-split`, `thm:pencil-flat-rank`, `thm:pencil-d-flat-rank` | No change. Sugihara 1986 §11.3's closing sentence confirms W84 and CW82 as the sources. |
| `lem:pencil-lifting-planes-motions` (P_q) | Optional history: Sugihara 1983 Remark 1 (pp. 317–318) and Table 2 (p. 320), the analogy between faces and rods (3-matroids), which is not the isomorphism. W84 Prop. 4.1 stays. |
| `sec:main-component-jj`, `thm:pencil-jj-equality` | At W89 Thm 3.1, cite Sugihara 1984 Conjecture 2 (p. 92, μ_S of p. 87). Attribute it precisely: the conjecture is the −4 sharp-lift count, and W89's −3 independence count is W89's extension (W89 p. 76). Sugihara 1986 §6.2 as presentation. |
| `lem:pencil-d-condition-linear` | Add Sugihara 1984 p. 80 eq. (1) (also Sugihara 1983 p. 314 and Sugihara 1986 §3.4 eq. (3.1)) beside W89 p. 78. |
| `lem:pencil-d-rank-collineation`, `lem:pencil-d-rank-scale-shift` | Scale-shift at d = 3: Sugihara 1984 eq. (10), p. 85, the picture-preserving map z ↦ γz + αx + βy + δ. Collineation: CW82 §3.6 stays. CW94 Remark 5.7 (pp. 279–280) is optional context. |
| `sec:pencil-duality`, `lem:pencil-self-dual` | No change for the pencil polarity. If O6 is written up: the Maxwell polarity is Maxwell 1870 p. 8, CW93 Defs 4.3–4.4 (p. 73) and CW94 Def. 4.3 and Remark 4.4 (p. 273), and the chapter's normal convention differs from it by a collineation. Lead: Whiteley 1991 "Weavings, sections…". |
| "pencil" | No change. |
| `def:pencil-d-configuration` | No change. Confirmed: no source in this cluster lifts by several heights (CW93 p. 58 and CW94 p. 261 defer 4-polytopes to an unpublished third paper; Rybnikov uses one height). Crapo–Ryan stays the only precedent. |
| `def:pencil-d-lift` (Part C) | Optional: Rybnikov 1999 §10, p. 504, beside W84 Def. 7.2. |
| `sec:pencil-roadmap`, introductions | The lineage: Maxwell 1864 p. 258 and Maxwell 1870 pp. 7–8 → Huffman 1977 pp. 476–479 and Mackworth 1973 pp. 124–125 → Sugihara 1983, 1984 → CW93 (Thm 3.2, Cor. 3.5, Thm 4.6, Cor. 4.11) and CW94 (Thm 4.4, Thm 5.1) → Rybnikov 1999 (Thm 5.1). |
| O3 (an observation, §6(c)) | CW93 Def. 4.2 and Thm 4.5(a); CW94 Prop. 4.1, Remarks 2.8, 3.2 and 5.8, Thm 3.1, Thm 5.1(ii) and p. 277; Sugihara 1986 §11.1; Mackworth 1973 p. 125; Maxwell 1870 pp. 7–8. Wording in §2. |
| O5 | "Planarity never enters": Sugihara 1984 p. 85 (§3.1). Where it enters Maxwell: CW93 p. 57 (cycle conditions automatic for planar graphs) and Rybnikov Thm 5.1 and p. 491. |

## Changes to the new/classical boundary

1. **None moves from new to classical.** In particular there is no pencil stratum, no hinge
   realization by lifting, no several-height lift read as a framework, and no self-dual pencil class
   in these ten sources.
2. **O3 is reclassified from "the agents' observation" to "classical mechanism, S_G instance new as
   far as found"** (§2). It is not contradicted.
3. **The carrier's attribution widens.** Sugihara 1984 (the scene equations, their linear space and
   dimension for any incidence structure, and the equality of the vertex and face descriptions) sits
   beside W84, which supplies the correspondence with frameworks.
4. **The attribution of Sugihara's conjecture is corrected** at every use of W89 Thm 3.1 (note §2,
   §5 Q1).
5. **Bibliographic facts.** CW93 runs 55–78, and `REFS.md`'s claim of no page numbers should be
   corrected. CW94 runs 259–281. CW93's in-text reference numbers are offset from its bibliography.

## Open, and who decides

- **Whiteley 1991, "Weavings, sections and projections of spherical polyhedra"**, *Discrete Appl.
  Math.* 32 or 33 (1991) 275–294; the volume differs between CW94 ref. [14] and CW93's bibliography
  [29]. CW93 p. 58 and CW94 p. 261 name it as the projective "cross-section" form of the reciprocal.
  It is the likeliest classical home of O6 and of reading P_q as a section. It is unread and not in
  `.refs/`; whether to fetch it is the PI's call.
- **Falk 1972 and Duda–Hart 1973**: Sugihara 1986 §1.3 credits them with the scene equations. Both
  are unread; citing them is the PI's call.
- Whether O3 goes into a chapter at all is §6(c), the PI's call.

## Appendix: the O3 check at θ(2,2,3) (exact rational arithmetic)

Not committed: the deliverable forbids touching the tree. This is the full script. It reproduces
the note's numbers and should be committed with the report if it is banked (the project's
committed-scripts rule). Output: `dim F(q) = 4`, `rank of gradient image = 3`, `dim motions of
(G,q) = 5`, `gradients are motions: True`, `rank(image+translations) = 3`,
`rank(image+rotation) = 4`.

```python
from fractions import Fraction as F
V = ['a','b','1','2','3','4']
E = [('a','1'),('1','b'),('a','2'),('2','b'),('a','3'),('3','4'),('4','b')]
q = {'a':(-2,0),'b':(2,1),'1':(0,1),'2':(0,-1),'3':(-1,2),'4':(1,3)}
N = {v:{v} for v in V}
for u,v in E: N[u].add(v); N[v].add(u)
ix = {v:i for i,v in enumerate(V)}
def rref(rows, n):
    M=[list(map(F,r)) for r in rows]; piv=[]; r=0
    for c in range(n):
        p=next((i for i in range(r,len(M)) if M[i][c]!=0),None)
        if p is None: continue
        M[r],M[p]=M[p],M[r]; M[r]=[x/M[r][c] for x in M[r]]
        for i in range(len(M)):
            if i!=r and M[i][c]!=0: f=M[i][c]; M[i]=[x-f*y for x,y in zip(M[i],M[r])]
        piv.append(c); r+=1
    return M, piv
rank = lambda rows: len(rref(rows, len(rows[0]))[1])
def null(rows, n):
    M,piv=rref(rows,n); out=[]
    for fc in [c for c in range(n) if c not in piv]:
        x=[F(0)]*n; x[fc]=F(1)
        for i,pc in enumerate(piv): x[pc]=-M[i][fc]
        out.append(x)
    return out
n=3*len(V); rows=[]          # unknowns per face v: (g_x, g_y, c); h_v(xi) = g.xi + c
for w in V:                  # point w: h_v(q_w) equal for all faces v containing w
    fs=[v for v in V if w in N[v]]
    for v in fs[1:]:
        r=[0]*n
        for s,f in ((1,fs[0]),(-1,v)):
            k=3*ix[f]; r[k]+=s*q[w][0]; r[k+1]+=s*q[w][1]; r[k+2]+=s
        rows.append(r)
S=null(rows,n); print('dim F(q) =',len(S))
G=[[s[3*ix[v]+j] for v in V for j in (0,1)] for s in S]
print('rank of gradient image =',rank(G))
R=[]
for u,v in E:
    r=[0]*(2*len(V)); d=(q[u][0]-q[v][0],q[u][1]-q[v][1])
    r[2*ix[u]],r[2*ix[u]+1]=d; r[2*ix[v]],r[2*ix[v]+1]=-d[0],-d[1]; R.append(r)
print('dim motions of (G,q) =',2*len(V)-rank(R))
print('gradients are motions:',all(sum(F(a)*b for a,b in zip(r,g))==0 for g in G for r in R))
rot=[c for v in V for c in (-q[v][1],q[v][0])]; tr=[[1,0]*len(V),[0,1]*len(V)]
print('rank(image+translations) =',rank(G+tr),' rank(image+rotation) =',rank(G+[rot]))
```
