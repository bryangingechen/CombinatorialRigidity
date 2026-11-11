# PENCIL-SCENES recon: the concurrence-geometry, polarity and hinge-class references

*Read-only recon, 2026-11-11, for `notes/PencilScenes.md` (§2, §3's table, §4's O1–O7) and
`lineage.md`. The cluster: Crapo 1984, 1989 and 1991; Whiteley's "Rigidity and polarity" I (1987) and
II (1989); Tay–Whiteley 1984; Lundqvist–Stokes–Öhman 2025. Tay 1989 was used only for a cross-check.
Page numbers are the printed ones unless marked "pdf p.".*

**How the sources were read.** Crapo 1984, 1989, 1991, RP-I, RP-II and LSÖ have usable text layers.
I read each one in full from the text layer and checked the load-bearing pages against the page images
(listed per source). Tay–Whiteley 1984 has no text layer, so I read all eight pages as images. REFS says
those pages are stored rotated by 90°, but the Read tool rendered them upright. In the text layers, the
figures and several bracket formulas (Crapo 1991 (13), (18)) are garbled. Nothing below depends on
them. **Verified** means seen on the page. **Derived** means my own algebra, not stated in any source,
and not checked by script or compiler. No script was run: the only processing was pypdf extraction of
text.

---

## 1. Crapo, "Concurrence geometries" (*Adv. Math.* 54 (1984) 278–301)

**Read:** pp. 278–301, all. Pages 293–295 checked against the page images.

- **The problem is O6's, as stated (p. 278, verified):** "to describe combinatorially the variety of
  configurations c of hyperplanes which can be constructed, given that the section of the configuration c
  on a fixed hyperplane H be a given geometric figure." It comes from describing "the space of
  infinitesimal motions (equivalently: parallel redrawings)" of a plane bar-and-joint structure.
- **§7, pp. 293–294, Theorem 4 (verified).** Fix a hyperplane H. The variable hyperplanes H_j have fixed
  sections A_j = H_j ∩ H, and "each variable hyperplane H_j has one degree of freedom of motion … its
  position can be determined by a single scalar c_j". With H at infinity, H_j is
  a_1j x_1 + … + a_kj x_k = c_j. Then k + 1 of them "meet at a point (are concurrent) in configuration c
  if and only if the corresponding k+1 columns of A′ have determinant zero", where A′ is A with c added
  as a (k+1)-st row. That condition is linear in c: c·f = 0, with f's entries the k×k cofactors of A.
  Theorem 4: the configurations, ordered by specialization, form a geometric lattice of rank n − k.
- **Derived: the match with the project.** Take the panel with normal b_v = (x_v, y_v, z_v, 1), as in
  `def:pencil-d-configuration` at d = 3. Send z = 0 to infinity (affine chart Z = 1). The panel becomes
  x_v X + y_v Y + W = −z_v. So Crapo's matrix A is the 3×n matrix of homogeneous picture points, and
  c = −z. Four panels are concurrent iff the four lifted points (q, z) are coplanar. The trivial
  configurations (all hyperplanes through one point, Crapo's "1 → R(A)", p. 298) are the row space of A,
  which is Aff(q). So the configurations over q modulo Aff(q) are an interval of Crapo's C(A), the flat
  cut out by the 4-tuples inside each closed neighbourhood. With the project's dim L(q) = 3 + def₂, that
  interval has rank def₂ (O1's quotient). Whiteley 1989 §5.1, p. 87, makes the same identification in
  words (verified in its text layer): "The 'lifting' extends this configuration to a set of planes in
  3-space with the given intersections on a fixed cutting plane z = 0. The equation for an edge
  constrains the four planes of the edge to share a point in 3-space. This interpretation is an example
  of Crapo's concurrence geometries [1]. It was in this geometric setting that the matrix A(H, X) first
  appeared."
- **p. 295, verified: the setting with several heights, named but not developed.** "A further
  generalization of these ideas results from the Laplace expansion of the determinant of an n+p-by-n+p
  matrix in terms of complementary minors of size p by p and n by n. This algebra arises in the
  concurrence problem where we replace the fixed hyperplane H by a fixed flat H of corank p … (k+p)-tuples
  of hyperplanes are then coordinatized by (n choose p)-vectors whose non-zero entries are Plücker
  coordinates drawn from matrices of size k by k+p. We shall not deal further with this generalization in
  the present paper." **Derived:** with k = 3 and p = d − 2, this is the polar form of
  `def:pencil-d-configuration`. In P^d, the panel with normal b_v = (x_v, y_v, z¹_v, …, z^{d−2}_v, 1)
  meets the fixed plane Z₁ = … = Z_{d−2} = 0 (corank d − 2) in P_q's body line, and it has d − 2 free
  scalars, the heights. One difference: Crapo's conditions, concurrence of (k+p)-tuples, have degree p in
  the heights jointly. The chapter's node condition (each z^i in L(q), so no closed neighbourhood rises in
  rank) is linear in each height separately. That fits O4 and W84 §7.2's Remark, and changes neither.
- **§6, Theorem 2 (p. 292) and Theorem 3 (p. 293).** In the plane (k = 2), S-drawings ≅ infinitesimal
  motions of a plane bar-and-joint structure whose bars run along the n lines. This is the classical
  parallel-redrawing correspondence that LSÖ (§2.2) and W89 §5 build on. It is not P_q.
- **§8, Theorem 7 (p. 298):** C(A) is the geometry of circuits of the columns of A. At k = 3 the height
  conditions are the circuits (affine dependencies) of the picture points that lie in a node. These are
  Crapo–Ryan's D(E).
- **Not in it:** hinges, bodies, rigidity ranks, panels with coplanar or concurrent hinges, polarity of
  body-hinge structures, and the merging lemma.

## 2. Crapo, "Applications of geometric homology" (LNCS 391 (1989) 213–224)

**Read:** pp. 213–224, all. Page 213 checked against the image. The PDF prints no venue and no number
on its first page; p. 214 is the first numbered page.

- **pp. 215–216 (verified):** for a space F of functions on a point set P and an "open family" E,
  generated by its maximal members, the "nodes": F(E) = {g : g|A ∈ F(A) for all A ∈ E}, the functions
  "locally in F, on E". "This mapping F … is called a sheaf." dim F(E) = β₀, the 0th Betti number. The
  characteristic χ = Σ μ(B) r_F(B) runs over the semilattice of intersections of nodes, and
  χ = β₀ − β₁ + β₂ − …. So β₀ = χ when the higher Betti numbers vanish (p. 216). With F = L (linear
  functions) and E = the closed neighbourhoods, F(E) is the project's L(q).
- **pp. 218–221, scene analysis (verified):** E = (abcd, abef, cdef) on six points. Here β₁ = 1 because
  the lines ⟨ab⟩, ⟨cd⟩, ⟨ef⟩ are concurrent, χ = 3, so β₀ = 4. "There is a function h, locally but not
  globally linear" (p. 219). Figure 2 (p. 220) adds **one** row h to M(L) and draws its graph in 3-space.
  dim L(E) = |P| − dim D(E), with D(E) spanned by the dependencies supported on nodes (p. 220). For
  polyhedral scenes, χ = 3f − 2a + s, and "β₀ − 4 is equal to the number of projective choices in the
  construction of a 3-dimensional model" (p. 221).
- **Several heights?** β₀ counts every locally linear function, so all the heights at once. But the paper
  builds one height at a time and does not restate Crapo–Ryan's E-lift. It cites Crapo–Ryan in its
  bibliography. Whether χ(E) = 3 + def₂(G) for S_G (that is, whether the higher Betti numbers vanish) is
  not checked here.
- **p. 224:** a conjecture on bar frameworks in 3-space through the sheaf of local isometries. It has no
  hinges and no pencils.

## 3. Crapo, "Invariant-theoretic methods in scene analysis and structural mechanics" (*J. Symbolic Comput.* 11 (1991) 523–548)

**Read:** pp. 523–548, all.

- **p. 523 (verified), the problem of lifting by several heights:** "we wish to evaluate its 'natural
  dimension', that is, we wish to detect whether the drawing is the projection of a higher-dimensional
  object, and if so, of what (maximal) dimension, and with what relative heights of its component parts.
  The problem is one of 'lifting' a lower-dimensional object into higher dimensions." On p. 540 this
  becomes the aim of "a general algorithmic approach to … special positions in which a plane figure lifts
  to higher dimensions". For S_G, O2 answers this question: the maximal dimension is P^{2+def₂}.
- **pp. 531–532 (verified), type I and type II realizations.** Type I: a height for each vertex, with
  "sets of cofacial vertices … coplanar". Type II: a height for each vertex and "also a plane P_A for each
  face", with the incidences preserved. They differ when a face's points are collinear: the face plane
  can then turn about the line. That is the role of admissibility in `lem:pencil-lifting-planes-dim`
  (F(q) ≅ L(q)).
- **p. 532:** "the rank of the space of spatial realizations of a given drawing … is equal to 7, the
  number of points, less the rank of the matrix N" (the syzygies on the faces). This is dim L(E), one
  height space. p. 533: "The subject has been more fully developed in papers on geometric homology [Crapo
  and Ryan, 1986; Crapo, 1989]."
- **p. 543:** Maxwell's theorem links scene analysis and plane mechanics through type II realizations
  (spherical polyhedra). That is background for O3. **p. 546 (§4.3):** the centres of relative motion of a
  flexible plane framework are a configuration of n hyperplanes in projective (n−2)-space, projected into
  the plane. This is a concurrence-geometry reading of bar frameworks, not of P_q.
- **Not in it:** the E-lift, hinges and polarity.

## 4. Whiteley, "Rigidity and polarity I: statics of sheet structures" (*Geom. Dedicata* 22 (1987) 329–362)

**Read:** pp. 329–362, all. Page 344 checked against the image.

- **What it polarizes (pp. 329–330, §3, Theorem 3.1 p. 339):** a bar-and-joint framework in 3-space ↔ a
  **hinged sheetwork**. Its sheets are rigid only within their plane ("The sheet will warp easily out of
  its plane, but is rigid in the plane", p. 338). It is **not** the body-hinge class, and **not** the
  panel ↔ molecular polarity. That polarity of body-hinge structures is CW82 §3.6, as the chapters
  already cite, and TW84 p. 33 (§6).
- **The self-polar pattern (§4, verified).** A jointed sheetwork is a bipartite incidence of planes
  (sheets) and points (joints) (Def. 4.1, p. 344). Its polar exchanges the two (Def. 4.3, p. 345), and
  Theorem 4.1 (p. 345) says "A jointed sheetwork and each of its polars have identical static
  properties". The same holds for sheet polyhedra (Prop. 5.1, p. 353).
  **Derived, bearing on `lem:pencil-self-dual`:** a pencil realization whose hinges are nonzero puts the
  points q_v and the planes n_v in the incidences q_w ∈ n_v for w ∈ N[v]. So it is a point–plane
  realization of S_G. S_G is self-dual, because w ∈ N[v] iff v ∈ N[w]. So "polarity exchanges normals and
  points" is RP-I's pattern applied to a self-dual incidence structure, read as a body-hinge framework.
  The Lean definition also allows zero hinges and coincident points, so the reading is exact only for
  nondegenerate realizations.
- **The section reading (p. 344, Remark, verified):** "These unusual copunctual sheetworks embody, in
  polar form, the entire theory of plane bar-and-joint frameworks. A more convenient, Euclidean, model of
  these structures is formed if we place the common point at infinity and take the cross-section of the
  entire structure with a plane normal to the direction of the common point. Each sheet becomes a
  line-segment (a rod) and each hinge becomes a point of contact of two rods (a joint). The allowed loads
  … are normal to the plane … The theory of these plane rod-and-joint frameworks will be presented in a
  separate paper, along with some applications to the scene analysis of line configurations ([29])."
  **Derived:** read with the points as normals, the **flat** configuration (q, 0) is exactly such a
  copunctual configuration. Every panel x_v X + y_v Y + W = 0 contains the vertical point at infinity,
  and its section by z = 0 is P_q's lines and pins. So this Remark is the nearest classical analogue of
  O6 at height 0, for sheetworks rather than rigid bodies.
- **"Pencil" (p. 351, proof of Theorem 4.5):** "Each incidence of a joint with a sheet permits a
  2-dimensional space of F (the pencil of line segments through the point in the plane)." This is the
  rank-2 fact of CW82 pp. 56 and 67, for forces.
- **Dimension (p. 361, verified):** "For dimensions greater than 3 we do not know of any plausible
  interpretation of the polars of statics and infinitesimal mechanics." The same page: "We have briefly
  presented the plane analogue of a sheetwork in Sections 3 and 6 – the jointed rod structures and woven
  rod structures. Historically, this theory actually was developed first." Reference [29] (p. 362) is
  "Jointed and Woven Rod Structures (to appear)".
- **The promised sequel:** p. 330 and p. 361 promise a second paper on the infinitesimal mechanics of the
  3-space polarity. RP-II is not that paper (§5).
- **Not in it:** bodies whose hinges are both coplanar and concurrent, scenes or liftings in 3-space,
  and the merging lemma. Theorem 4.6 (pp. 351–352), which merges two coplanar sheets sharing two joints,
  is a geometric identification for the jointed-sheetwork count 2i = 3a + 3b − 6. It is not the S_G
  merging lemma.

## 5. Whiteley, "Rigidity and polarity II: weaving lines and tensegrity frameworks" (*Geom. Dedicata* 30 (1989) 255–279)

**Read:** pp. 255–279, all. Pages 255 and 264 checked against the images.

- **Content:** rods in the plane, lifted into 3-space. A weaving (§2, Def. 2.2 p. 259) keeps over and
  under crossings. A grillage (§4, Def. 4.1 p. 267) keeps contact at the crossings. Each line
  Ax + By + 1 = 0 gets "lifting numbers" (C, D), its lift lying on the plane z = Cx + Dy (§2.1, p. 257).
  Vertical forces act as weighted points on the lines (Def. 4.2, p. 268). Theorem 4.4 (p. 268): a grillage
  is flat iff it is statically rigid. Theorem 4.5 (p. 269): a generic grillage is independent iff
  |E′| ≤ 2|V′| − 3, "polarizing Laman's theorem". p. 256: "This connection is the explicit plane version
  of the duality described in Whiteley [10]" (that is, RP-I).
- **Is it "Lashed and woven rods"?** W82's bibliography (p. 38, checked against the image) lists "Lashed
  and Woven Rods", "Champlain Regional College, St. Lambert, Qué., to appear", with the annotation "The
  projective duals of plane bar and joint frameworks: rigid lines with motions and static forces normal to
  the plane". RP-I (1987) calls the same plane theory "Jointed and Woven Rod Structures (to appear)".
  RP-II matches all three on content: grillages are the jointed (lashed) rods, weavings are the woven rods,
  and both are polars of plane frameworks with motions and forces normal to the plane. **Verdict: yes, by
  inference, with stronger evidence than before.** None of the three papers states the identification.
  This series' "Part II" is the rods paper, not the mechanics sequel that RP-I promised.
- **The polarity of §3.2 (p. 264, verified):** it "takes the plane point (a, b) to the line L:
  ax + by + 1 = 0". The printed conic reads "x² + y² 1 = 0", with the sign dropped. **Derived:** P_q's
  body line, the line with normal (x_v, y_v, 1), is exactly this polar of the picture point q_v. JJ's
  rod-and-pin line p₁x + p₂y = 1 (TR §5, p. 12) is the same map with p = −q. Neither JJ nor the chapter
  says so.
- **Cross-section (Theorem 4.16, p. 274, verified):** a grillage on the dual skeleton of a spherical
  polyhedron has a nontrivial self-stress iff "there exists a spatial polyhedral configuration … with the
  grillage as a projective cross-section". It is credited to a Whiteley preprint, "Weavings, sections and
  projections of polyhedra". This is the second classical "section" statement next to O6.
- **Derived, optional, for O3:** O3's face gradients are a motion of the bar framework (G, q). Rotated by
  90°, they are a lifting of the RP-II grillage on the polar lines of q, which are P_q's body lines, with
  crossings at P_q's pins. The reason: the crossing ℓ_u ∩ ℓ_v is perpendicular to q_u − q_v.
- **Not in it:** 3-space hinges, pencils, and S_G.

## 6. Tay–Whiteley, "Recent advances in the generic ridigity [sic] of structures" (*Structural Topology* 9 (1984) 31–38)

**Read:** pp. 31–38, all, as page images. The text is bilingual; the English column was read.

- **p. 33 (verified, the end of the body-and-hinge section):** "Many body and hinge structures are built
  under additional constraints. For example in architecture 'flat' panels may be used in which all hinges
  are coplanar. In molecular chemistry, we can model molecules by rigid atoms hinged along the 'bond
  lines' so that all hinges to an atom are concurrent. This is the natural projective dual of the
  architectural condition."
- **p. 34 (verified):** **Conjecture 1** (Tay and Whiteley): "A multi-graph is generically rigid for hinged
  structures in n-space iff it is generically rigid for hinged structures in n-space with all hinges of
  body v_i in a hyperplane H_i of the space." Its Remark: "For the plane (n = 2 with all pins along a
  line), this conjecture was made 5 years ago, but remains unsolved." Then: "Only in 3-space does projective
  duality convert a hinge structure to a new hinge structure." Definition 5 defines identified body and
  hinge frameworks. Theorem 3 is the identified case in the plane, with the count 2i ≥ 2h + 3b − 3.
  **Conjecture 2** is the identified count in n-space.
- **W89's "[11, Conjecture 2]" (W89 p. 91):** at n = 2, TW84's Conjecture 2 gives the count of TW84's
  own Theorem 3, already proved there. So W89 Theorem 5.4, whose clause (iii) puts all of a body's joints
  on one line, settles the collinear-pins conjecture, which is **Conjecture 1** with its n = 2 Remark,
  generalized to identified structures. This confirms `lineage.md` and §2. W89's reference list also
  misnames the paper ("Recent progress in the generic rigidity of structures").
- **Not in it:** hinges that are both coplanar and concurrent, scenes, liftings and Maxwell. The
  bibliography (pp. 37–38) has **12** entries by my count; `lineage.md` says 13.

## 7. Lundqvist–Stokes–Öhman, "When is a planar rod configuration infinitesimally rigid?" (*Discrete Comput. Geom.*, Online First copy)

**Read:** pdf pp. 1–24, all. The copy prints no volume and no page numbers.

- **Main theorem (Theorem 4.1, pdf p. 19, verified):** "Let S = (P, L, I) be an incidence geometry such
  that S^C has a realization as a regular proper string configuration in R². Then all cone graphs of S are
  generically rigid in R² if and only if every regular proper string configuration realizing S^C in R² is
  infinitesimally rigid." Combined with pdf p. 9 ("a rod configuration realizing S is infinitesimally rigid
  if and only if …" its S^C string configurations are), it reads, as §5.2 (pdf p. 21) puts it: a regular
  proper rod configuration realizing S is infinitesimally rigid iff a (any) cone graph of S is generically
  rigid in the plane. "Regular" (pdf p. 18) means that the rows of the concurrence geometry matrix
  M(S, ρ) (pdf p. 6, named after Crapo's concurrence geometries) are independent on every sharply
  independent set of incidences.
- **Against W89 Theorem 5.4:** LSÖ's Theorem 2.4 (pdf p. 8) restates it. Theorem 4.1 "extends his result
  to hypergraphs that do not necessarily have realizations as independent body and joint frameworks"
  (abstract) and "coincides with Whiteley's version" in the independent case (pdf p. 3).
- **Against JJ TR Theorem 7.1:** JJ give the **rank**, r_RP(G) = 3|V| − 3 − def(G), for a graph without
  isolated vertices at generic lines. LSÖ give only **rigid / flexible**. Their objects are hypergraphs,
  with several rods through a joint, and their hypothesis is regularity, not generic lines. For the dual
  of a graph, their result "essentially coincides with the planar case of Theorem 1.1" (pdf p. 3), the
  molecular theorem. That corresponds to JJ's rigidity statement, TR Theorem 7.3, not to the rank formula
  of 7.1.
- **Is it the d = 2 case of P_q? Not in the sense the chapters need.** pdf p. 2 says "a planar panel and
  hinge framework is a planar rod configuration in which two rods can meet at each joint". So P_q, a rod
  configuration realizing the dual of G, is one of LSÖ's objects (derived). But the chapters' d = 2
  statement is the **rank** of P_q, dim L(q) = 3 + def₂, which is JJ TR 7.1. LSÖ do not give it. Their
  properness can also fail at an admissible q: three collinear picture points give concurrent body lines,
  hence coincident pins (derived). LSÖ contain no lifting, scene or height. §6 (pdf p. 22) leaves higher
  dimensions open. Cite LSÖ optionally, as the hypergraph neighbour of W89 Theorem 5.4.
- Lemma 3.3 (pdf p. 12) merges two minimally rigid subgraphs of an independent graph that share ≥ 2
  vertices. It is a Laman-count merging fact, credited "without proof" to Fekete–Jordán–Whiteley, and it is
  not the S_G merging lemma.

## 8. Cross-checks

- **Tay 1989, p. 271 (verified):** "Our results do not deal with body and hinge structures where (i) all
  the hinges on each of the bodies are concurrent (useful in molecular chemistry) or (ii) all the hinges
  on each of the bodies are coplanar … We conjecture that these results will remain true for these two
  types of structures." The two cases are separate. `lineage.md` row 3 stands.
- **W89 §5.1 and §5.3** were re-read for §1 and §6 (pp. 76–77, 87, 91–94). They agree with the note's §2
  entry and with `lineage.md`.

## 9. Bibliographic data (from the PDFs)

| Source | As printed | Not printed (from REFS / Crossref) |
|---|---|---|
| Crapo 1984 | "Concurrence Geometries", Henry Crapo; "Advances in Mathematics 54, 278-301 (1984)" | issue 3, DOI 10.1016/0001-8708(84)90043-4 |
| Crapo 1989 | "Applications of Geometric Homology", Henry Crapo; pages 214–224 numbered (first page 213 unnumbered) | venue (Geometry and Robotics, Toulouse 1988, LNCS 391, Springer), DOI 10.1007/3-540-51683-2_32. Crapo 1991 cites it as "Applications de l'Homologie Géométrique": use the printed English title |
| Crapo 1991 | "Invariant-Theoretic Methods in Scene Analysis and Structural Mechanics", Henry Crapo; "J. Symbolic Computation (1991) 11, 523-548"; received 9 Dec 1989 | issue 5–6, DOI 10.1016/S0747-7171(08)80118-6 |
| RP-I | "Rigidity and Polarity I: Statics of Sheet Structures", Walter Whiteley; "Geometriae Dedicata 22 (1987), 329-362"; Reidel | issue 3, DOI 10.1007/BF00147940. RP-II cites it as "…Statics of Sheetworks" |
| RP-II | "Rigidity and Polarity II: Weaving Lines and Tensegrity Frameworks", Walter Whiteley; "Geometriae Dedicata 30 (1989) 255-279"; Kluwer | issue 3, DOI 10.1007/BF00181341. No "plane" in the printed subtitle |
| TW84 | "Recent Advances in the Generic Ridigity of Structures" (sic), Tiong-Seng Tay and Walter Whiteley; "Structural Topology #9, 1984"; pp. 31–38 printed | none (the journal has no DOIs). The existing key `tayWhiteley1984` matches |
| LSÖ | "When is a Planar Rod Configuration Infinitesimally Rigid?", Signe Lundqvist, Klara Stokes, Lars-Daniel Öhman; Discrete & Computational Geometry, DOI 10.1007/s00454-023-00617-7; © 2023, accepted 2 Nov 2023 | 73(1) (2025) 25–48 |

---

## 10. §3's table: proposed citation changes

| §3 row | Proposed change (this cluster only) |
|---|---|
| `sec:main-component-carrier`, `def:pencil-lifting-space` | Optional: Crapo 1989 pp. 215–216 (L(q) as the sheaf of locally linear functions on the closed neighbourhoods; dim = β₀), beside Crapo–Ryan §8. The scene definitions stay W84 and Sugihara |
| `lem:pencil-lifting-planes-dim` | Optional: Crapo 1991 pp. 531–532 (type I and type II realizations differ only on collinear faces, which is admissibility's role). The primary stays W84 Prop. 4.1 |
| `lem:pencil-flat-split`, flat ranks | Optional: RP-I p. 344 Remark as the analogue of the flat member (copunctual panels, whose section is a rod-and-joint structure with normal loads; sheetworks, not bodies). "The 3 in-plane dimensions are in no source" stands |
| `lem:pencil-lifting-planes-motions` (P_q) | Add: P_q's body lines are the RP-II §3.2 (p. 264) polars of the picture points (derived), and JJ's rod-and-pin parametrization is the same map. Optional: LSÖ pdf p. 2 (planar panel-hinge = rod configuration) |
| `sec:main-component-jj`, `thm:pencil-jj-equality` | Name **TW84 Conjecture 1 and its n = 2 Remark (p. 34)** as the plane conjecture, never "[11, Conjecture 2]". LSÖ Theorem 4.1 only as the hypergraph rigidity extension of W89 Theorem 5.4: not a rank formula, and no dim L(q) |
| `lem:pencil-d-condition-linear` | Optional: Crapo 1984 p. 294 (concurrence is linear in the configuration scalars), the polar of W89 p. 78 |
| `lem:pencil-d-rank-collineation`, `…-scale-shift` | No change |
| `sec:pencil-duality`, `lem:pencil-self-dual` | TW84 p. 33 verified (quote above). Add TW84 p. 34 ("Only in 3-space does projective duality convert a hinge structure to a new hinge structure") and RP-I p. 361 (no polar mechanics above dimension 3). Cite RP-I §4 (Defs 4.1 and 4.3, Theorem 4.1, pp. 344–345) and Prop. 5.1 (p. 353) for the pattern of self-polar point–plane classes |
| "pencil" | Optional: RP-I p. 351 (a pencil of forces at a joint in a sheet spans 2 dimensions), beside CW82 pp. 56, 67 |
| `def:pencil-d-configuration` (d − 2 heights) | Add **Crapo 1984 p. 295** (the corank-p generalization: hyperplanes with fixed sections on a fixed flat of corank p, each with p scalars; named, not developed; derived to be this definition's polar form at p = d − 2) and **Crapo 1991 p. 523** (the "natural dimension" problem), beside Crapo–Ryan §8. Crapo 1989 and 1991 compute dim L(E) but do not restate the E-lift |
| `def:pencil-d-lift` (Part C) | No change |
| `sec:pencil-roadmap`, introductions | The lineage paragraph can name Crapo's concurrence geometries (the section on a fixed plane) through W89 §5.1, and RP-I and RP-II for the polarity theme |
| O6 (observation) | **Crapo 1984 p. 278 and §7 (Theorem 4, pp. 293–294) with W89 §5.1 p. 87.** Analogues: RP-I p. 344, RP-II Theorem 4.16 (p. 274) |
| O2, O3, O5 (observations) | O2: Crapo 1984 p. 295 and Crapo 1991 p. 523 beside Crapo–Ryan. O3: optionally RP-II §4 (derived reading). O5: optionally Crapo 1989 pp. 216–219 (the coefficient spaces on intersections of nodes) |

## 11. The new/classical boundary

- **Moves to classical: O6's cutting-plane reading.** The configurations of panels over q with section P_q
  on z = 0 are Crapo's concurrence configurations (1984 §7), and W89 §5.1 already identifies them with
  scene liftings. What stays new is reading those panels as a **body-hinge framework** (hinges as meets of
  adjacent panels) and its rank.
- **Moves earlier: lifting by several heights over a plane picture.** Crapo 1984 p. 295 names the polar
  setup with p = d − 2 free scalars per panel, two years before Crapo–Ryan's E-lift, but does not develop
  it. Crapo 1991 p. 523 states the "maximal dimension" lifting problem. The item "reading the lifts by
  several heights as hinge frameworks with a rank" stays new.
- **Self-duality of the pencil class: new as a statement, classical in pattern (the PI decides).** No source
  in this cluster states it. It is RP-I §4's self-polar point–plane pattern applied to the self-dual
  incidence structure S_G (derived, exact for nondegenerate realizations). I would demote it from "new" to
  "an immediate consequence, not stated in the sources".
- **Unchanged:** the pencil stratum itself. None of Crapo 1984, 1989, 1991, RP-I, RP-II, TW84, LSÖ or Tay
  1989 considers bodies whose hinges are both coplanar and concurrent. `lineage.md`'s verdict and ROADMAP
  §39's verdict stand. The pencil realization theorem and the steps A, B and C are untouched.
- **Contradictions:** none with O1–O7 or `lineage.md`. Small corrections to `lineage.md`: TW84's
  bibliography has 12 entries, not 13. RP-II has now been read, and its printed subtitle is "Weaving Lines
  and Tensegrity Frameworks". RP-I's printed subtitle is "Statics of Sheet Structures".
- **Merging lemma:** not in any of these sources. LSÖ Lemma 3.3 and RP-I Theorem 4.6 merge parts for
  other counts and are not it.
- **Open, not checked:** whether Crapo 1989's χ(E) equals 3 + def₂(G) for S_G, that is, whether the
  higher Betti numbers vanish. That would be a third route to dim L(q), and it would need a committed
  script.
