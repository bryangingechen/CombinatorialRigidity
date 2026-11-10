# PENCIL-SCENES recon, Q3 and Q4: the pencil stratum's lineage, and the classical sources missing from `.refs/`

*Banked as delivered by a read-only recon agent on 2026-11-09. The coordinator's spot-checks, and the
corrections they found, are in `notes/PencilScenes.md` §5; read that first.*

Read-only literature recon, 2026-11-09, for `notes/PencilScenes.md` §5 Q3 and Q4. Page numbers are
the printed ones unless marked "pdf p.". "Verified" for a reference means checked against Crossref
metadata (DOI given), the publisher's or repository's record, or the printed first page of the
paper itself. Anything else is marked unverified or inferred.

**What was read in full or in the relevant part:** Whiteley 1984, 1989, 1999 and 2005, Crapo–Whiteley 1982,
Tay 1989, Jackson–Jordán 2006 (TR), Katoh–Tanigawa 2011 and Tanigawa 2012 (from `.refs/`).
Downloaded and read for this recon (none of them saved in the repo): Tay–Whiteley 1984, Crapo–Whiteley 1993, Crapo–Ryan 1986, the
Crapo–Whiteley 1994 abstract and introduction, Sugihara's book (author's web release), Schulze–Whiteley's Handbook chapter
(preliminary version), Nixon–Schulze–Whiteley 2021, Lundqvist–Stokes–Öhman (arXiv v2), Karpenkov–Mohammadi–Müller–Schulze
(arXiv). **Not read (no free copy found):** Huffman 1977, Sugihara 1983 and 1984, Whiteley's
"Rigidity and polarity" I and II. Their content below comes from the papers that cite them.

---

## Q3. Does any prior work treat the pencil stratum?

### Verdict: no (only partial lineage)

The searches found **no result, conjecture or discussion of body-hinge frameworks whose hinges at each body
are both coplanar and concurrent**, the pencil stratum. That covers 3-space and every other dimension,
and it covers any rank or rigidity statement. The classical literature treats each
specialization separately: coplanar (panel-hinge) and concurrent (molecular), with the polarity between
them. It also treats the fully flat case of a molecule lying in one plane, and the plane analogue
(collinear pins). Nor did anything turn up that uses liftings of a plane picture to *construct* 3-space
body-hinge, panel or molecular realizations. The lifting correspondences in the literature run the other way,
from a given picture to its stresses or plane motions. ROADMAP §39's 2026-07-23 verdict
stands with the new leads. The closest items:

| # | Source, place | What it says | How close |
|---|---|---|---|
| 1 | Crapo–Whiteley 1982 §3.5, p. 67; figure caption p. 56 | p. 67: "the linear combinations of two extensors on intersecting lines … form the vector space of all coordinates of lines through this point in the plane of the original two lines. This family of lines is called a **flat pencil** of lines." p. 56: "Three lines have rank 2 only if they lie in a flat pencil: they are coplanar and copunctual." | The term, and the fact that a pencil of hinges spans only a 2-dimensional subspace of screw space. The natural citation for the word "pencil" and for that fact. |
| 2 | Tay–Whiteley 1984, pp. 33–34 | p. 33: "In architecture 'flat' panels may be used in which all hinges are coplanar. In molecular chemistry, we can model molecules by rigid atoms hinged along the 'bond lines' so that all hinges to an atom are concurrent. This is the natural projective dual of the architectural condition." p. 34, Conjecture 1 (the molecular conjecture, quoted below). p. 34: "Only in 3-space does projective duality convert a hinge structure to a new hinge structure." | The two specializations named separately, as polar duals. Never both together. The last sentence bears on `sec:pencil-duality` and on why the polarity has no d ≥ 4 analogue (Nixon–Schulze–Whiteley 2021 §10.4 says the same). |
| 3 | Tay 1989, p. 271 | After characterizing identified body-hinge structures (Thms 7.1–7.3): "Our results do not deal with body and hinge structures where (i) all the hinges on each of the bodies are concurrent (useful in molecular chemistry) or (ii) all the hinges on each of the bodies are coplanar (useful in prefab buildings). We conjecture that these results will remain true for these two types of structures." | The same two specializations, conjectured separately, for identified hinges. |
| 4 | Whiteley 1999, p. 25 | Three lines "which are coplanar and concurrent … generate the linearly dependent rows … A hinge-body cycle of length three on these three hinges will be shaky." | A pencil of three hinges on a 3-cycle. It is the dependence that the project's pencil cycle section (`sec:pencil-cycle`) handles. |
| 5 | Whiteley 1999, pp. 35–36 (Example 24, Corollary 25) | Molecular structures with the atoms of a face coplanar ("polyhedral molecules"). Example 24 is a *plane* hexagonal ring: the cycle equations reduce to 3, which leaves "a 3-parameter solution space" of twists. | A molecule lying entirely in one plane is the *flat* member of the pencil stratum: every atom's bonds are coplanar and concurrent, but in one common plane. This is the zero-height lifting, not the stratum's generic point. |
| 6 | Whiteley 1989 Thm 5.4 (p. 92); Jackson–Jordán 2008 Thm 7.2; Lundqvist–Stokes–Öhman 2025 | The plane analogue: body-and-pin (or body-and-joint) frameworks with each body's pins collinear. Whiteley proves the isostatic hypergraph case and Jackson–Jordán the general graph case (they give the rank formula). Lundqvist–Stokes–Öhman (*Discrete Comput. Geom.* 73(1) (2025) 25–48, DOI 10.1007/s00454-023-00617-7, verified; arXiv:2112.01960) extend Whiteley's Theorem 5.4 to arbitrary hypergraphs ("rod configurations", via a "cone graph"). §6 of the arXiv v2 says that higher dimensions are open. | The 2-dimensional side of the project's proof: P_q is pin-collinear. No lifting to 3-space appears in any of the three. |
| 7 | Katoh–Tanigawa 2011 §1.2, pp. 650–651; Schulze–Whiteley 2017 Thm 61.2.4; Nixon–Schulze–Whiteley 2021 §10.4 | The molecular model: "all the hinges incident to a body are intersecting each other at the center of the body. Such a hinge configuration is called hinge-concurrent". Its dual is panel-hinge, and Katoh–Tanigawa attribute the polarity invariance to Crapo–Whiteley 1982. | The project's pencil realization, with adjacent points distinct, *is* a hinge-concurrent (molecular) realization: hinge uv = line q_u q_v, by `def:pencil-panel-realization`. Each atom's bonds are also coplanar, so every closed neighbourhood is coplanar (trigonal-planar atoms). The chapter already gives this molecular reading. The search found no rigidity result for this class of molecules beyond the globally flat case (row 5). |
| 8 | Whiteley 1982 pp. 14, 18–21; Whiteley 1984 Prop. 4.1, §5.3; Crapo–Whiteley 1993, 1994 | Liftings of a plane picture ↔ motions of a plane plate structure, or ↔ self-stresses (Maxwell). | Already in the note's §2. These are the lineage of the *carrier* (the scene space). None of them builds a 3-space hinge realization from a lifting. |
| 9 | Crapo–Ryan 1986 §8, pp. 52–53 (Q4 §6 below) | For an image in projective space of any rank and a family of "nodes", the scenes are the "E-locally linear" height functions. The "E-lift" adds *all* of them at once as new coordinates: "the lift of a configuration P is that preimage of P under projection which is of highest possible rank, given the restriction that no node is increased in rank". | The nearest prior object to the project's several heights and universal lift (note O2, `def:pencil-d-configuration`). With nodes = closed neighbourhoods, the E-lift is O2's universal lift. Still no hinge realization. |

**Who decides:** the PI, at the open. The chapter could say "new, as far as we know", cite rows 1–2
for the term and the two separate specializations, and cite rows 6–8 for the classical ingredients.

### Whiteley 1989's p. 93 conjecture: exact statement and status

> "Remark. This theorem is the plane analogue of an important conjecture about spatial structures. The
> appropriate definitions are given in [11].
> Conjecture. A bipartite graph can be realized in 3-space as an infinitesimally rigid identified body and
> hinge structure if and only if it can be realized as an infinitesimally rigid identified body and hinge
> structure with all hinges of each body in a single plane." (p. 93)
>
> "For the special case where each hinge connects only two bodies, we do have a characterization of the
> graphs [11], but the methods used here do not extend to solve even this special case of the conjecture."
> (p. 94)

Here [11] is Tay–Whiteley 1984, whose Definition 5 (p. 34) defines an *identified* body and hinge framework.
It is a bipartite graph G = ⟨B, H; I⟩ of bodies and hinges, so a single hinge may be shared by several bodies. Status:

- **The graph case (each hinge on two bodies)** is Tay–Whiteley 1984 Conjecture 1 at n = 3, the molecular conjecture.
  Katoh–Tanigawa 2011 proved it in every dimension, and Jackson–Jordán 2008 proved it at d = 2. That proof covers "coplanar".
  The "concurrent" version follows by Crapo–Whiteley's polarity, but only in 3-space.
- **The identified case in 3-space:** no proof found, and nothing found that calls it settled. Tay 1989 (p. 271) conjectured the
  same thing for identified structures (concurrent or coplanar). Lundqvist–Stokes–Öhman settle the plane version for all
  hypergraphs and leave higher dimensions open. Read this as "open as far as found", not as verified open.
- **Coplanar *and* concurrent:** neither conjecture asks for it, and no later paper found does.

**Corrections to `notes/PencilScenes.md` §2 (Whiteley 1989 entry):** the conjecture is on p. 93, but the quoted
"the methods used here do not extend" is on **p. 94**. The conjecture is about **identified** structures, of which the
molecular conjecture is the two-bodies-per-hinge case. Also, Whiteley 1989 p. 91 says Theorem 5.4 "settles a
conjecture about body and joint frameworks in the plane [11, Conjecture 2]". In Tay–Whiteley 1984, however, the collinear-pins
plane conjecture is the n = 2 remark under **Conjecture 1** (p. 34: "For the plane (n = 2 with all pins along a
line), this conjecture was made 5 years ago, but remains unsolved"). Conjecture 2 there is the counting characterization
of identified structures in n-space. A chapter citing this should name TW84 Conjecture 1, not "Conjecture 2".

### Tay–Whiteley 1984: obtainable, and what it says

- **Reference (verified from the scan and the repository record):** T.-S. Tay, W. Whiteley, "Recent advances in the generic
  ridigity of structures" (sic, "Ridigity" in the printed title), *Structural Topology* 9 (1984) 31–38. Bilingual,
  French then English in parallel columns. The bib key `tayWhiteley1984` matches.
- **Free:** UPCommons (Universitat Politècnica de Catalunya), which hosts the full run of *Structural Topology* as open access.
  Record https://hdl.handle.net/2099/1017; PDF
  https://upcommons.upc.edu/server/api/core/bitstreams/fa6301ea-dc67-4622-8a71-13150fec6a26/content
  (`st9-06-a3.pdf`, a scan with no text layer). Under the `.refs/` convention it would be
  `tay-whiteley-1984-recent-advances-generic-rigidity.pdf`.
- **Contents:** a survey of the August 1983 Bielefeld workshop on applied matroid theory. Theorem 1 (Tay, body-bar).
  Theorem 2 (Tay and Whiteley, body-hinge). The remarks quoted above (p. 33). Conjecture 1: "A multi-graph is
  generically rigid for hinged structures in n-space iff it is generically rigid for hinged structures in n-space with
  all hinges of body v_i in a hyperplane H_i of the space" (p. 34). Identified structures: Definition 5, Theorem 3 (plane,
  "an easy consequence of Laman's theorem") and Conjecture 2 (n-space count), all p. 34. Identified body-and-screw
  structures: Theorem 4 (Whiteley), p. 35. Bar and joint frameworks: Laman, Lovász–Yemini, Dress's Conjecture 3 (pp. 35–37).
- **Not in it:** scene analysis, liftings, Maxwell, reciprocal figures, or any mention of hinges coplanar *and* concurrent.
  The bibliography (pp. 37–38) has 13 items, all on rigidity or matroids.

### Whiteley 1999 and Whiteley 2005

- **Whiteley 1999** (`whiteley1999`; printed p. = pdf p. + 20): rows 4–5 above. It also has p. 27, Definition 4 (molecular structure);
  p. 29, Conjecture 9 (a "translation of a conjecture of Tay and Whiteley"); pp. 29–30, the polar hinge-panel structures with the
  polarity in a sphere (Example 11); p. 41, Theorem 33 (twists of a molecular structure ↔ self-stresses of the polar "block
  sheetwork", which it calls "the polar of a correspondence between statics of bar-and-joint frameworks and bendings of
  hinge-panel structures", i.e. Crapo–Whiteley 1982). It has **no liftings or scene analysis**, apart from citing the Handbook
  chapter, and nothing on atoms with coplanar bonds beyond the flat ring.
- **Whiteley 2005** (in `.refs/`, no bib key): §5, p. S121. Theorem 5.1 (body-bar to body-hinge, credited to Tay–Whiteley [23,24])
  and Conjecture 5.2 (the molecular conjecture). It names the two "gaps": (a) the five bars must form a hinge; (b) "all the hinge
  lines h_ab of any body for an atom a are concurrent in a central point". It mentions double and peptide bonds only as locks
  (p. S117), and has **nothing on planar atoms, liftings or scenes**.

### Web search, 2026-11-09 (standard mode; mathematical terms only)

Queries covered: "flat pencil" with hinges and body-hinge; "concurrent and coplanar" or "coplanar and concurrent" hinges;
identified body-hinge with coplanar hinges on hypergraphs; molecular frameworks with planar (sp²) atoms; liftings used to build
panel-hinge or molecular realizations; Maxwell–Cremona and body-hinge; scenes over pictures with coplanar closed neighbourhoods.
**Nothing on the pencil stratum turned up.** What the post-1990 lifting and scene literature does contain:

- **Surveys.** B. Schulze, W. Whiteley, "Rigidity and scene analysis", Chapter 61 of *Handbook of Discrete and
  Computational Geometry*, 3rd ed. (Goodman, O'Rourke, Tóth eds., CRC Press, 2017), pp. 1593–1632. The pages come from the
  preliminary version at https://csun.edu/~ctoth/Handbook/chap61.pdf, dated 10 Aug 2017. Its §61.3.1 has the Picture Theorem (Thm 61.3.1),
  "conjectured by Sugihara and proven in [Whi88a]" (= Whiteley 1989). §61.4 has Maxwell's theorem (Thm 61.4.1), the
  first complete proof credited to Klein–Wieghardt 1904, and the refinement to spaces of liftings credited to [CW94].
  Thm 61.2.3 (from [CW82]): a spherical bar framework has a self-stress iff the body-hinge framework on the dual graph,
  with hinge lines p_i p_j, is flexible. §61.1.4 credits [Whi89] with this: polarity "turns plane infinitesimal motions into lifting motions of the
  lines into 3-space". Theorem 61.2.4 is the panel-hinge and molecular theorem. **The chapter does not cite Whiteley 1984 (DAM)**,
  and it says nothing about pencils.
  A. Nixon, B. Schulze, W. Whiteley, "Rigidity through a projective lens", *Appl. Sci.* 11(24) (2021) 11946,
  DOI 10.3390/app112411946 (verified; open access). Its §8 covers polarity, §10.4 molecular and panel-hinge frameworks
  (polarity "does not extend to higher dimensions"), and §14 points to a companion preprint, "Projective Geometry of Scene Analysis,
  Parallel Drawing and Reciprocal Drawings" (2021), for which no published version was found. It has nothing on pencils.
- **Liftings since 1990.** K. Rybnikov, "Stresses and liftings of cell-complexes", *Discrete Comput. Geom.* 21(4) (1999)
  481–517, DOI 10.1007/PL00009434 (verified): liftings of non-spherical complexes. Karpenkov–Mohammadi–Müller–Schulze,
  "A differential approach to Maxwell–Cremona liftings", arXiv:2312.09891 (2023). Karpenkov–Servatius–Servatius,
  "Liftings of surfaces in the plane", arXiv:2505.18841 (2025): Maxwell–Cremona liftings for non-planar frameworks.
  Kaszanitzky–Schulze, "Lifting symmetric pictures to polyhedral scenes", *Ars Math. Contemp.* 13(1) (2016) 31–47,
  DOI 10.26493/1855-3974.876.16a (verified). Lundqvist–Schulze–Stokes, "Symmetric polyhedral scenes and parallel
  redrawings", arXiv:2609.27605 (Sept 2026). All of them concern stresses, symmetry or parallel redrawings. **None constructs
  hinge realizations.** Rybnikov and Karpenkov–Servatius–Servatius bear on observation O5 of the note (where planarity enters Maxwell).

---

## Q4. Sources the classical papers cite that are not in `.refs/`

Each entry gives the reference and how it was verified, what bears on the lifting space or the correspondence, whether a free copy exists, and
whether a chapter should cite it.

### 1. Crapo–Whiteley on plane stresses and projected polyhedra

The preprints carry different titles over the years. Whiteley 1982 (bibliography, p. 37) and Whiteley 1984 [2] cite "Stressed frameworks and
projected polyhedra" (preprint, 1977). Whiteley 1989 [3] cites "Plane stresses and projected polyhedra" (preprint, 1986).
The published outcome:

- **(a) H. Crapo, W. Whiteley, "Plane self stresses and projected polyhedra I: the basic pattern", *Structural
  Topology* 20 (1993).** Verified from the repository record and the scan. **The page range is unsettled, but 55–78 is
  likelier:** Whiteley's own 1996 bibliography ([CrW2], under the shorter title "Plane stresses and projected polyhedra") and Karpenkov et al.
  cite 55–78. The repository record says 55–79, and so does the 1994 paper's citation of Zbl 0793.52006. A Whiteley CV
  (seen only in a search snippet) says 55–68. The scan has 24 pages, which gives 55–78 if the numbering is contiguous, but its pages carry no
  journal page numbers. Record https://hdl.handle.net/2099/1091; free PDF
  https://upcommons.upc.edu/server/api/core/bitstreams/4321ab26-d9c7-45a4-97fc-b5370f0fbe70/content (OCR).
  **Content:** the three-way Maxwell correspondence (self stress ↔ reciprocal ↔ spatial polyhedron), for spherical and for
  general oriented polyhedra. For general ones it needs cycle conditions: the vector sum and the moment sum of the forces across every
  face-edge cycle must vanish (the scan's third page, p. 57 if the pages run on from 55). These are "trivially true for the self stresses on any planar graph". Corollary 4.11 is
  "essentially the original theorem of Maxwell". It promises a second paper with "the full vector space of reciprocals and
  spatial liftings of a plane drawing". Identifying the 1977 and 1986 preprints with this paper is an inference (same programme,
  same title family), not something either paper states.
  **Cite:** yes, wherever a chapter states Maxwell's theorem or contrasts the pencil lifting with it (observations O3 and O5).
  It is the careful modern statement, and its cycle condition is the "path condition" of the note's O5.
- **(b) H. Crapo, W. Whiteley, "Spaces of stresses, projections and parallel drawings for spherical polyhedra",
  *Beiträge zur Algebra und Geometrie* 35(2) (1994) 259–281.** Verified against the EMIS abstract page; Karpenkov et al. cite
  259–282. It has no DOI. Free (PostScript): https://ftp6.gwdg.de/pub/EMIS/journals/BAG/vol.35/no.2/b35h2wh1.ps.gz,
  abstract `…/b35h2wh1.abs`. **Content (abstract and introduction):** isomorphisms between "(a) the affine space of polyhedra with a
  fixed projection; (b) the vector space of self stresses of the framework; and (c) the space of reciprocal figures"
  and, dually, the spaces of parallel drawings. In effect it is the promised second paper, for spherical polyhedra.
  **Cite:** yes, if a chapter states that for planar graphs the lifting space is the self-stress space plus the trivial
  liftings. That is this paper's statement. Schulze–Whiteley 2017 §61.4 cites it for the same thing.
- **(c) "Stressed frameworks and projected 4-polytopes"** (marked "to appear" in Whiteley 1982 and 1984 [4]; Whiteley 1984,
  pp. 293–294, uses it for a 3-space Maxwell analogue). It was apparently never published. Karpenkov et al. (2023, ref. [8]) cite H. Crapo,
  W. Whiteley, "3-stresses in 3-space and projections of polyhedral 3-surfaces: reciprocals, liftings and parallel
  configurations", unpublished manuscript, 1993. **Not citable as a source.** It is relevant only to Q2 (Part C).
  Crapo–Whiteley 1993 also cites a "Plane self stresses and projected polyhedra III: non-spherical surfaces" (preprint,
  1992). No published version was found.

### 2. Sugihara

- **(a) K. Sugihara, "An algebraic and combinatorial approach to the analysis of line drawings of polyhedra",
  *Discrete Appl. Math.* 9(1) (1984) 77–104, DOI 10.1016/0166-218X(84)90092-1** (verified). Whiteley 1984 cites it as
  Nagoya technical report 8207 [11]; that this is the same paper is inferred from the identical title. **Content (per Whiteley 1989, p. 76, and Sugihara 1986, §6.2):**
  Sugihara's conjecture that a generic picture lifts to a sharp scene iff i′ ≤ v′ + 3f′ − 4 on every set of incidences
  meeting at least two faces. He proved it for special classes (trihedral and convex objects; 3-connected spherical polyhedra). Whiteley 1989 proves it in full.
  Not read; free availability not checked. **Cite:** yes, at any use of Whiteley 1989 Theorem 3.1 (Q1): "conjectured
  by Sugihara [1984], proved by Whiteley [1989]". Schulze–Whiteley 2017 and Sugihara's book (§6.2) attribute it the same way.
- **(b) K. Sugihara, *Machine Interpretation of Line Drawings*, MIT Press (Artificial Intelligence series), 1986;
  ISBN 0-262-19254-3** (the ISBN comes from bookseller listings and is unverified). **Free and legal:** the author's page
  https://www.isc.meiji.ac.jp/~kokichis/openbooks/openbookse.html says "the MIT Press kindly allowed me to post all the book pages";
  the PDF is https://www.isc.meiji.ac.jp/~kokichis/openbooks/mild.pdf. It is a 2006 LaTeX re-typesetting, so **its page numbers
  differ from the print edition: cite by section.** **Content:** §5.1, the linear system (vertex heights and face planes) and its
  degrees of freedom (Thm 5.1); §6.2, Thm 6.1 (the equations are independent iff |V(X)| + 3|F(X)| ≥ |X| + 3) and Thm 6.2
  (generic reconstructibility), "first conjectured by Sugihara … proved completely by Whiteley (1988)", with the proofs in §6.3
  "due to Whiteley (1988)"; §6.4, Thm 6.3 (the generic degrees-of-freedom matroid); Ch. 11, gradient space and reciprocal diagrams
  (§11.1), Maxwell's correspondence (§11.3), and a generic correspondence between incidence structures with 4 degrees of freedom and
  Laman graphs (§11.4). §1.3 *Short History* is the best short account of where the problem came from (next item).
  **Cite:** yes, as the presentation of scene analysis that a chapter follows, beside Whiteley 1989. Schulze–Whiteley also
  list it as the overview.
- **(c) K. Sugihara, "A unifying approach to descriptive geometry and mechanisms", *Discrete Appl. Math.* 5(3) (1983)
  313–328, DOI 10.1016/0166-218X(83)90004-5** (verified). Whiteley 1984 (p. 269) credits it with promoting "a unified approach to
  the two fields based on the similarity of the sparse systems of linear equations … and the similar matroid structures".
  Not read. **Cite:** optional, only if a chapter credits who first pointed out the common linear structure of scenes and rigidity.
- **(d) Sugihara's 1981 Nagoya preprint, "A correspondence between line drawings of polyhedra and plane skeletal structures"** (Whiteley 1984
  [13], credited with "a combinatorial correspondence"). Its published form is probably the book's §11.4 (inferred).
  **Don't cite the preprint.**

### 3. Huffman (and the origin of the scene-analysis problem)

- **(a) D. A. Huffman, "A duality concept for the analysis of polyhedral scenes", in E. W. Elcock, D. Michie (eds.),
  *Machine Intelligence 8*, Ellis Horwood, Chichester, 1977, pp. 475–492.** Verified against the volume's contents on
  https://www.doc.ic.ac.uk/~shm/MI/mi8.html (ch. 23 at p. 475, ch. 24 at p. 493; that page misprints the year as "1877"), and against
  Sugihara's bibliography. Whiteley 1982 lists the US co-publisher, John Wiley, New York. Not read, and no free copy found.
  **Content (secondary sources only):** dual pictures in gradient space for line drawings of polyhedra. Whiteley 1984 (p. 269) says Maxwell's
  correspondence "has been partially rediscovered in scene analysis by Huffman, in the form of geometric dual figures".
  **Cite:** only in a history sentence, beside Maxwell, as the rediscovery in scene analysis.
- **The origin as Whiteley cites it.** Whiteley 1984 (p. 269) cites Maxwell [9, together with the Crapo–Whiteley 1977 preprint
  and Whiteley 1982], Huffman 1977 [7], Sugihara's 1981 preprint [13] and Sugihara 1983 [12]. On p. 271, "the standard linear equations for polyhedral scenes
  and line drawings [5, 11, 12]" are Duda–Hart, Sugihara 1984 and Sugihara 1983. **Duda–Hart is cited as 1975 but is R. O. Duda, P. E. Hart,
  *Pattern Classification and Scene Analysis*, Wiley, 1973** (verified via a 1973 review in *Artificial Intelligence* 4,
  DOI 10.1016/0004-3702(73)90004-0, and Sugihara's bibliography). Whiteley 1989 cites Sugihara 1984 [9] for the conjecture,
  Imai 1985 [6] and Sugihara 1986 [10] for the O(i²) algorithms, and Crapo's concurrence geometries [1, 2] (next item). Sugihara's
  §1.3 history gives Huffman 1971 and Clowes 1971 for line labelling, and Huffman 1971/1977 and Mackworth 1973 for the gradient-space
  reciprocal ("rediscovered"). It credits **Falk 1972 and Duda–Hart 1973** with first pointing out the linear equations a
  pictured polyhedron must satisfy. History references, if wanted:
  - J. C. Maxwell, "On reciprocal figures and diagrams of forces", *Phil. Mag.* (4) 27 (1864) 250–261,
    DOI 10.1080/14786446408643663 (verified). **This is not the existing bib key `maxwell1864`**, which is Maxwell's
    "On the calculation of the equilibrium and stiffness of frames", pp. 294–299, in the same volume. A chapter citing the reciprocal
    paper needs a new key. Also J. C. Maxwell, "On reciprocal figures, frames, and diagrams of forces", *Trans. Roy. Soc.
    Edinburgh* 26 (1870) 1–40, DOI 10.1017/S0080456800026351 (verified).
  - A. K. Mackworth, "Interpreting pictures of polyhedral scenes", *Artificial Intelligence* 4(2) (1973) 121–137,
    DOI 10.1016/0004-3702(73)90003-9 (verified; Crossref misspells the author "Macworth"). Free at
    https://www.cs.ubc.ca/~mack/Publications/AI73.pdf.
  - D. A. Huffman, "Impossible objects as nonsense sentences", *Machine Intelligence 6* (Meltzer, Michie eds.), Edinburgh
    Univ. Press, 1971, pp. 295–323. Pages confirmed by Sugihara's bibliography and a journal reference; the aitopics.org
    download link from search results returned 404.
  - M. B. Clowes, "On seeing things", *Artificial Intelligence* 2 (1971) 79–116, DOI 10.1016/0004-3702(71)90005-1; G. Falk,
    "Interpretation of imperfect line data as a three-dimensional scene", *Artificial Intelligence* 3 (1972) 101–144,
    DOI 10.1016/0004-3702(72)90044-6 (both verified).
  - W. Whiteley, "Realizability of polyhedra", *Structural Topology* 1 (1979) 46–58 (verified from the record; free at
    https://hdl.handle.net/2099/527, a scan with no text layer; only the abstract was read). It asks "which plane line drawings portraying the edge graph
    of a combinatorial polyhedron are actually the projection of … a plane-faced polyhedron". Sugihara credits it with a
    "figure-construction approach". Low priority.
  - Not needed for the pencil chapters, but leads for ORIGAMI: Huffman, "Curvature and creases: a primer on paper", *IEEE Trans.
    Comput.* C-25 (1976) 1010–1019, DOI 10.1109/TC.1976.1674542, and Kanade, "A theory of Origami world", *Artificial
    Intelligence* 13 (1980) 279–311, DOI 10.1016/0004-3702(80)90004-1 (both verified).

### 4. Whiteley, "Lashed and woven rods"

- Whiteley 1982 (bibliography, p. 38) lists it as "Champlain Regional College, to appear", annotated "The projective duals of plane bar
  and joint frameworks: rigid lines with motions and static forces normal to the plane". Whiteley 1984 [21] uses it in §5.4
  (p. 289) for "A bar and joint framework in the plane has a shake iff its dual line picture in the plane has a non-trivial
  line scene in space".
- **Published, by inference, as W. Whiteley, "Rigidity and polarity II: weaving lines and tensegrity frameworks", *Geom.
  Dedicata* 30(3) (1989) 255–279, DOI 10.1007/BF00181341** (metadata verified; Crossref's subtitle is "II: Weaving lines and
  tensegrity frameworks", while the Handbook and Nixon–Schulze–Whiteley write "…plane tensegrity frameworks"). That this is the same work as the 1982
  preprint is inferred from matching content: Schulze–Whiteley §61.1.4 says it "turns plane infinitesimal motions into lifting motions
  of the lines into 3-space", and its reference list cites Tarnai's grillage duality. Neither paper states the identification. Not read; Springer, not free.
- Companion: W. Whiteley, "Rigidity and polarity I: statics of sheet structures" (Crossref subtitle; often cited as
  "…sheetworks"), *Geom. Dedicata* 22(3) (1987), DOI 10.1007/BF00147940. Crossref has no pages; Whiteley 1999 and Nixon–Schulze–Whiteley
  give 329–362.
- **Cite:** only if a chapter discusses the polar of the plane-motion side (line scenes ↔ plane motions). Low priority for the
  pencil chapters, whose polarity (`sec:pencil-duality`) is the 3-space point–plane one of Crapo–Whiteley 1982.

### 5. Others found that bear on the carrier

- **H. Crapo, "Concurrence geometries", *Adv. Math.* 54(3) (1984) 278–301, DOI 10.1016/0001-8708(84)90043-4** (verified).
  Whiteley 1989 (p. 77) says its Section 2 results "turned out to be a reformulation of [Crapo's] work on general position
  concurrence geometries", and §5.1 reads the scene matroid polarly as parallel redrawing. **Cite:** at the polar reading
  (Whiteley 1996's Remark 8.3.2, and the note's §2), if a chapter uses it. Not read.
- H. Crapo, "The combinatorial theory of structures", in *Matroid Theory* (Lovász, Recski eds.), Colloq. Math. Soc. János
  Bolyai 40, North-Holland, 1985, pp. 107–213 (Whiteley 1989 [2]). **Unverified** (no DOI found).
- H. Imai, "On combinatorial structures of line drawings of polyhedra", *Discrete Appl. Math.* 10(1) (1985) 79–92,
  DOI 10.1016/0166-218X(85)90060-5 (verified). Algorithmic only; no need to cite.
- S. Tanigawa, "Generic rigidity matroids with Dilworth truncations", *SIAM J. Discrete Math.* 26(3) (2012) 1412–1439,
  DOI 10.1137/100819473 (verified). It reproves Tay's characterization of identified body-hinge frameworks (Tay 1989, Thms 7.1–7.3),
  which appears to settle Tay–Whiteley 1984's Conjecture 2, the generic count. That is my reading, unverified. It is relevant only if a
  chapter mentions identified hinges.

### 6. Whiteley 1996's [CrW4] and [CRy]: scenes in higher dimensions

These were forwarded from the `pencil-d.tex` ledger. Whiteley 1996 (`whiteley1996`, author's preprint pagination) cites both.
On pdf p. 44, at the end of the first paragraph of §8.3 *Polarity to scene analysis*, it says "(Also see [Cr3,4,CRy,CR] for a related analysis of liftings.)". [CrW4] is cited in §15
(pdf p. 102), for working directly with non-simplicial cells, and in Remark 16.3.1 (pdf pp. 123–124), for "skeletal r-rigidity
beyond 3-rigidity in 3-space". The background: Whiteley 1984 §7.2 (p. 292) defines scenes in (K+1)-space over K-space pictures and
says it has "not seen this discussed elsewhere" (the coordinator checked this). Whiteley 1989 §4 then proves the generic count for
such scenes ("i′ ≤ v′ + kf′ − (k+1)", p. 76), with one height and hyperplane faces.

- **[CRy] H. Crapo, J. Ryan, "Spatial realizations of linear scenes", *Structural Topology* 13 (1986) 33–68.**
  Whiteley 1996 misspells it "relizations". Verified from the repository record (pp. 33–68) and the scan, whose printed pages are
  pdf p. + 32. The journal assigns no DOIs. **Free:** https://hdl.handle.net/2099/1037; PDF
  https://upcommons.upc.edu/server/api/core/bitstreams/fe2f8040-19c5-46f0-92b6-f140dc4af7c3/content (OCR, bilingual).
  **Content:** §1 (p. 34): given an image P and a family E of "nodes" (point sets that must keep their rank, i.e. stay collinear or
  coplanar), a "scene over the given image" is a point set projecting to it that preserves the ranks of nodes. "The set … of all scenes having a given
  two-dimensional projection … forms a linear space." The aim is to compute its rank. **§8 (pp. 52–53) works in any dimension:**
  "an image: a set P … in a projective space S of rank k … The intention is to construct a scene of higher dimension, such
  that the rank of each node in the scene is the same as its rank in the image". Each E-scene is "a height function f whose
  restriction f|A to any node of E is linear", called "E-locally linear". L(E) is the space of these functions, and its orthogonal complement D(E)
  is spanned by the dependencies supported on nodes. Adding a basis of L(E) as new rows of the coordinate matrix gives "the E-lift of P", which
  is "that preimage of P under projection which is of highest possible rank, given the restriction that no node is increased
  in rank". "The central objective … is accurately to compute this rank" r(E), and §9 uses geometric (sheaf and cosheaf) homology to do it. §3 treats
  "Scene analysis in Flatland" (a plane figure over a line). Research problem 6 (p. 64) proposes comparing "the sheaf of locally-linear
  functions (for images and scenes)" with "the sheaf of local isometries (for linkages …)" to restate Maxwell–Cremona
  homologically.
  **Does it treat higher-dimensional scenes or liftings? Yes.** It allows images of any rank. Its E-lift lifts by *all* independent
  locally linear functions at once, so the lift's rank is dim L(E) and not just one more than the image's. Take P to be a plane picture q of G and the nodes to be the
  closed neighbourhoods N[v]. A node of three or more points in general position has rank 3 in the plane, so it must stay coplanar.
  L(E) is then the note's L(q), and the E-lift is O2's "universal lift … whose closed neighbourhoods each span a plane". The
  claim that every scene is a linear projection of the E-lift is my reading of the construction (each locally linear function is a combination of
  the lift's rows); the paper does not state it. It is also the nearest classical precedent for taking d − 2 heights at once
  (`def:pencil-d-configuration`). The paper has no hinges, rigidity ranks or counts. **Cite:** yes, at O2 and at the
  multi-height configuration of `pencil-d.tex`, as the source of the space of locally linear functions and the
  lift of highest rank. It is relevant to Q2 too. Crapo's follow-ups, cited beside it in Whiteley 1996 and not read: H. Crapo,
  "Applications of geometric homology", in *Geometry and Robotics* (Toulouse 1988), LNCS 391, Springer, 1989, pp. 213–224,
  DOI 10.1007/3-540-51683-2_32; H. Crapo, "Invariant-theoretic methods in scene analysis and structural mechanics",
  *J. Symbolic Comput.* 11(5–6) (1991) 523–548, DOI 10.1016/S0747-7171(08)80118-6. Both verified on Crossref.
- **[CrW4] H. Crapo, W. Whiteley, "3-stresses in 3-space and projections of 4-polytopes: reciprocals, liftings and
  parallel configurations"**, cited as a York University preprint, 1994. **Unpublished:** no journal version found. Karpenkov et al. (2023, ref.
  [8]) cite it as "3-stresses in 3-space and projections of polyhedral 3-surfaces: reciprocals, liftings and parallel
  configurations", unpublished manuscript, 1993. It is the descendant of "Stressed frameworks and projected 4-polytopes" (item 1(c)).
  **Higher-dimensional?** Yes, judging by the title and the citing passages (not read): it is Maxwell one dimension up, with
  3-stresses in 3-frameworks, liftings of 3-space pictures to polyhedral 3-surfaces in 4-space (one height, hyperplane facets), and
  their reciprocals. That is Whiteley 1984 §7.2's single-height pattern, not several heights. **Not citable as a source.** For its
  published counterpart cite Rybnikov 1999 (liftings and stresses of d-complexes in d-space), and Whiteley 1989 §4 for the generic count.

### Summary: worth adding to the bibliography (and to `.refs/`, the PI's call)

1. Crapo–Whiteley 1993 (*Structural Topology* 20; free): Maxwell's theorem with the cycle conditions (O3, O5).
2. Crapo–Whiteley 1994 (*Beitr. Algebra Geom.* 35; free): the lifting space ≅ stresses, for planar graphs.
3. Sugihara 1984 (*DAM* 9): the conjecture behind Whiteley 1989 Thm 3.1 (Q1).
4. Sugihara 1986 book (free): the standard presentation of scene analysis; cite by section.
5. Maxwell 1864 *reciprocal figures* (Phil. Mag. 27, 250–261): a new key, distinct from `maxwell1864`.
6. Tay–Whiteley 1984 (already `tayWhiteley1984`): now obtainable, so cite its pages (Conjecture 1, p. 34; the polarity remark, p. 33).
7. Crapo–Ryan 1986 (*Structural Topology* 13, 33–68; free): the space of locally linear functions, and the E-lift of highest rank,
   in any dimension. It is the classical source for O2's universal lift and for scenes with several heights (pencil-d, Q2).
8. Optional: Crapo–Whiteley 1982 pp. 56, 67 for "flat pencil" (key exists); Huffman 1977 and Mackworth 1973 for history;
   Lundqvist–Stokes–Öhman 2025 for the plane hypergraph molecular theorem; Rybnikov 1999 for non-spherical liftings.
