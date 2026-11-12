# REFS.md — citation detail and the reference PDFs in `.refs/`

Read-on-demand reference (not session-start orientation). The citation rule
itself is the top-level `CLAUDE.md` *Referencing prior work*; this file
carries its detail (the pre-commit scan, the verification bar with its
precedents, the cross-check references) and how to read the local PDFs.

## The citation scan and the verification bar

*(Moved from the top-level `CLAUDE.md` *Referencing prior work* on
2026-10-05.)*

Concretely, **proactively scan your blueprint / notes / commit-
message prose before commit** and ask, for each substantive
mathematical step:

- Whose result is this? (A named theorem, a classical lemma, a
  technique attributed in standard references.)
- Have I cited it? If "no", does this commit cite something else
  that subsumes it (e.g., the blueprint chapter's section preamble),
  or am I silently asserting the result?
- If "yes" — verify the citation per the bar below before commit.

The bar to *add* a citation is low; the bar to *leave the prose
uncited* should be high. When in doubt, cite the standard reference
and let the next reviewer judge whether it's needed.

The verification bar:

Hallucinated section pointers (e.g. *"Whiteley §3"* with no paper
specified) and mis-attributions (crediting a populariser or
surveyor instead of the original prover) are the failure modes — once
written down they propagate through future sessions and read as
authoritative.

The minimum bar:

- **Author + year resolve to a real publication.** Confirm title,
  journal/series, volume, and page range against a primary source
  (DOI landing page, publisher metadata, NASA ADS).
- **"X §N" references hold.** §N must exist in X and contain what
  you claim. A previous-session "Jordán §3.1" was actually about
  M-circuits, not the Henneberg decomposition the prose claimed —
  if you cannot quickly verify, write *"classical"* or *"see X for a
  survey"* without a section number rather than guess one.
- **Attribution names who proved the result.** A survey or textbook
  is fine as a *"presentation we follow"* pointer alongside the
  primary citation, not in place of it. *"Abstract rigidity matroid
  (Whiteley)"* was wrong — Graver 1991 introduced the concept; the
  Servatius SIAM survey explicitly says so.

Jordán 2016 (*Combinatorial Rigidity: Graphs and Matroids in the
Theory of Rigid Frameworks*, MSJ Memoirs 34) is the project's
de-facto cross-check for rigidity-theory attributions; its
bibliography resolves most papers the blueprint or notes would cite.
For **abstract matroid-theory** attributions (matroid union,
submodular/polymatroid, Edmonds partition — Phases 12–15), the
cross-check is Oxley 2011 (*Matroid Theory*, 2nd ed.); Schrijver's
*Combinatorial Optimization* (Vol. B) carries clean modern proofs.
Local PDF copies under `.refs/` (gitignored) are convenient when
present.

## Reading PDFs in `.refs/`

Reference PDFs accumulate under `.refs/` (gitignored). To grep or
extract text, use the `pypdf` library inside the blueprint Python venv;
it reads PDFs directly without external system tools. (The standard
`Read` tool's `pages` parameter also renders PDF pages as images, as of
2026-11-09, verified on the scan `whiteley-1982-motions-stresses-projected-polyhedra.pdf`;
pypdf extracts nothing from a scan, so a scan needs the `Read` tool.)

```sh
cd blueprint && source .venv/bin/activate
# pypdf is not in requirements.txt; install once per fresh venv.
pip install pypdf >/dev/null

python3 - <<'PY'
import pypdf
r = pypdf.PdfReader('/path/to/.refs/jordan-2016-msj-memoirs.pdf')
print('pages:', len(r.pages))
print(r.pages[0].extract_text()[:4000])      # title + TOC
# Or grep for keywords across the whole PDF:
for i, page in enumerate(r.pages):
    if 'Maxwell' in page.extract_text():
        print(f'page {i+1} mentions Maxwell')
PY
```

Page numbering caveat: printed pages may not start at 1, so *paper
p.N* often corresponds to *pdf page (N − offset)*. Check page 1 to
calibrate. (Jordán's printed pages start at 33, so *Jordán p.N* =
*pdf page (N − 32)*.)

## Wanted references: `.refs/WANTED.md`

Sources the notes cite or need and `.refs/` does not hold are listed in
`.refs/WANTED.md`. Like the PDFs it is gitignored and local to the main
checkout, so it is absent from a fresh clone and from a git worktree; an
agent in a worktree reports a wanted source to the coordinator instead.
Add a row when a recon or a chapter names a source that should be read
and is not held: the full citation (marked **Unverified** unless checked
to the bar above), why it is wanted and for which phase, the note that
cites it, whether a free copy is known, and the filename it should get
under the naming convention below. Whether to fetch is the PI's call.
When a PDF arrives, rename it to the convention, add its row to the
catalogue below, and delete its row from `WANTED.md`.

## Catalogue of `.refs/`

`.refs/` is gitignored, so a fresh clone has none of these PDFs; this table lists what the main checkout holds, one row per file. New PDFs follow the naming convention `<surnames>-<year>-<short-title-slug>.pdf` (lowercase ASCII, hyphens, first-author surname or up to three surnames, the publication year, 3–6 title words, a `-tr` suffix for a technical-report version). A PostScript download is converted to PDF (`ps2pdf`); an OCR-text-only archive keeps its extension, with an `-ocr` suffix. A whole volume held for one chapter is named after the chapter, and its row gives the chapter's pdf pages. "Bib key" is the entry in `blueprint/src/bibliography.bib`, if any.

| File | Reference | Bib key | Notes |
|---|---|---|---|
| `asimow-roth-1978-rigidity-of-graphs.pdf` | L. Asimow, B. Roth, The rigidity of graphs, *Trans. Amer. Math. Soc.* 245 (Nov. 1978) 279–289. | `asimowRoth1978` | Printed pages start at 279 (pdf page = p. − 278). The text layer garbles the mathematics. |
| `barnabei-brini-rota-1985-on-the-exterior-calculus.pdf` | M. Barnabei, A. Brini, G.-C. Rota, On the exterior calculus of invariant theory, *J. Algebra* 96 (1985) 120–160. | `barnabeiBriniRota1985` | Printed pages start at 120. |
| `berg-jordan-2003-algorithms-graph-rigidity-scene-analysis.pdf` | A. R. Berg, T. Jordán, Algorithms for graph rigidity and scene analysis, in G. Di Battista, U. Zwick (eds.), *Algorithms – ESA 2003*, Lecture Notes in Comput. Sci. 2832, Springer, 2003, pp. 78–89. | — | Venue, editors and pages are printed on p. 78. Printed pages start at 78 (pdf page = p. − 77). The figures leave runs of `/0/1` in the text layer. Renamed from `berg2003.pdf`. |
| `chen-cruickshank-kitson-2023-block-and-hole.pdf` | B. G. Chen, J. Cruickshank, D. Kitson, Block-and-hole graphs: constructibility and (3,0)-sparsity, arXiv:2309.06804v1 [math.CO] (13 Sep 2023). | — | arXiv preprint; no venue on the PDF. |
| `crapo-1984-concurrence-geometries.pdf` | H. Crapo, Concurrence geometries, *Adv. Math.* 54 (3) (1984) 278–301, DOI 10.1016/0001-8708(84)90043-4. | — | Printed pages start at 278 (pdf page = p. − 277). Issue and DOI from Crossref. |
| `crapo-1989-applications-of-geometric-homology.pdf` | H. Crapo, Applications of geometric homology, in J.-D. Boissonnat, J.-P. Laumond (eds.), *Geometry and Robotics* (Toulouse 1988), Lecture Notes in Comput. Sci. 391, Springer, 1989, pp. 213–224, DOI 10.1007/3-540-51683-2_32. | — | The PDF prints neither venue nor volume: the volume, editors and DOI are from Crossref, the series number 391 from the notes (Crossref omits it). Printed pages start at 213 (pdf page = p. − 212). |
| `crapo-1991-invariant-theoretic-methods-scene-analysis.pdf` | H. Crapo, Invariant-theoretic methods in scene analysis and structural mechanics, *J. Symbolic Comput.* 11 (5–6) (1991) 523–548, DOI 10.1016/S0747-7171(08)80118-6. | — | Printed pages start at 523 (pdf page = p. − 522). Issue and DOI from Crossref. |
| `crapo-ryan-1986-spatial-realizations-linear-scenes.pdf` | H. Crapo, J. Ryan, Spatial realizations of linear scenes, *Structural Topology* 13 (1986) 33–68. | — | Scan with an OCR text layer (French accents garbled). Bilingual, French and English in parallel columns; printed pages start at 33 (pdf page = p. − 32). Renamed from UPCommons' `st13-05-a2-ocr.pdf`. |
| `crapo-whiteley-1982-statics-of-frameworks.pdf` | H. Crapo, W. Whiteley, Statics of frameworks and motions of panel structures, a projective geometric introduction, *Structural Topology* 6 (1982) 43–82. | `crapoWhiteley1982` | Bilingual (French then English); printed pages start at 43 (pdf page = p. − 42). |
| `crapo-whiteley-1993-plane-self-stresses-projected-polyhedra-i.pdf` | H. Crapo, W. Whiteley, Plane self stresses and projected polyhedra I: the basic pattern, *Structural Topology* 20 (1993) 55–78. | — | Scan with an OCR text layer (unreliable in places). Bilingual, English and French in parallel columns. 24 pdf pages. The printed page numbers are cut off at the outer margin; the visible digits fit pdf page = p. − 54, and the article ends with its bibliography on p. 78 (`notes/pencil-scenes/refs-liftings.md` §1). 55–78 is also what Whiteley 1996's and Crapo–Whiteley 1994's bibliographies give; the UPCommons record and Zbl say 55–79. Renamed from UPCommons' `st20-08-a4-ocr.pdf` (https://hdl.handle.net/2099/1091). |
| `crapo-whiteley-1994-spaces-of-stresses-spherical-polyhedra.pdf` | H. Crapo, W. Whiteley, Spaces of stresses, projections and parallel drawings for spherical polyhedra, *Beiträge Algebra Geom.* 35 (2) (1994) 259–281. | — | Converted with Ghostscript's `ps2pdf` from the EMIS PostScript `b35h2wh1.ps.gz` (https://ftp6.gwdg.de/pub/EMIS/journals/BAG/vol.35/no.2/). Bitmap fonts: the text layer drops the fi/ff ligatures ("rst" for "first"). Printed pages start at 259 (pdf page = p. − 258). |
| `doubilet-rota-stein-1974-on-the-foundations-of-combinatorial-theory-ix.pdf` | P. Doubilet, G.-C. Rota, J. Stein, On the foundations of combinatorial theory: IX, Combinatorial methods in invariant theory, *Studies in Applied Mathematics* 53 (3) (Sept. 1974); the paper starts at p. 185 per its contents page. | — | Printed pages start at 185 (pdf page = p. − 184). |
| `edmonds-1965-minimum-partition-matroid.pdf` | J. Edmonds, Minimum partition of a matroid into independent subsets, *J. Res. Nat. Bur. Standards Sect. B* 69B (1–2) (Jan.–June 1965) 67–72. | `edmonds1965` | Printed pages start at 67 (pdf page = p. − 66); the running text OCR has spurious spaces. |
| `finbow-ross-whiteley-2009-rigidity-of-spherical-frameworks.pdf` | W. Finbow, E. Ross, W. Whiteley, The rigidity of spherical frameworks: swapping blocks and holes (preprint, compiled 21 Oct 2018). | — | Preprint; no venue, volume or pages on the PDF. |
| `franzblau-2000-generic-rigidity-molecular-graphs-ear-decomposition.pdf` | D. S. Franzblau, Generic rigidity of molecular graphs via ear decomposition, *Discrete Appl. Math.* 101 (2000) 131–155. | `franzblau2000` | Printed pages start at 131 (pdf page = p. − 130). The text layer drops some ligatures and word spaces. |
| `henneberg-1911-graphische-statik-starren-systeme-ocr.zip` | L. Henneberg, *Die graphische Statik der starren Systeme*, B. G. Teubners Sammlung von Lehrbüchern auf dem Gebiete der mathematischen Wissenschaften XXXI, Teubner, Leipzig and Berlin, 1911. | `henneberg1911` | **OCR text only: no page images, so none of its 394 figures.** One text file per scanned page of a New York Public Library copy (768 files, `33433089972164/00000NNN.txt`); file N is printed p. N − 22. Search with `zipgrep '<pattern>' <zip>`, read a page with `unzip -p <zip> '*/00000030.txt'` (p. 8). |
| `huffman-1977-duality-concept-polyhedral-scenes.pdf` | D. A. Huffman, A duality concept for the analysis of polyhedral scenes, in E. W. Elcock, D. Michie (eds.), *Machine Intelligence 8: Machine Representations of Knowledge*, Ellis Horwood, Chichester, 1977, pp. 475–492. | — | The whole volume (640 pdf pages, scan with an OCR text layer); the paper is ch. 23, pdf pp. 479–496 (pdf page = p. + 4). The volume also holds Huffman's ch. 24, "Realizable configurations of lines in pictures of polyhedra" (pp. 493–509), and Mackworth's ch. 25, "How to see a simple world" (from p. 510). |
| `hunt-1967-screw-axes-mobility-linear-complex.pdf` | K. H. Hunt, Screw axes and mobility in spatial mechanisms via the linear complex, *J. Mechanisms* 2 (3) (1967) 307–327, DOI 10.1016/0022-2569(67)90005-5. | — | The running head prints "Volume 3"; Crossref gives volume 2, issue 3, which the notes follow. Printed pages start at 307 (pdf page = p. − 306). |
| `imai-1985-combinatorial-structures-line-drawings-polyhedra.pdf` | H. Imai, On combinatorial structures of line drawings of polyhedra, *Discrete Appl. Math.* 10 (1985) 79–92, PII 0166-218X(85)90060-5. | — | Scan with an OCR text layer that garbles the formulas (read page images for them). Printed pages start at 79 (pdf page = p. − 78). Renamed from the publisher's `1-s2.0-0166218X85900605-main.pdf`. |
| `jackson-jordan-2006-pin-collinear-tr.pdf` | B. Jackson, T. Jordán, Pin-collinear body-and-pin frameworks and the molecular conjecture, EGRES Technical Report TR-2006-06 (31 Aug 2006). | `jacksonJordan2008pin` | Tech-report version of the published paper, `jackson-jordan-2008-pin-collinear-body-and-pin-frameworks.pdf`, whose numbering differs throughout. |
| `jackson-jordan-2008-on-the-rigidity-of-molecular-graphs.pdf` | B. Jackson, T. Jordán, On the rigidity of molecular graphs (preprint dated 16 Nov 2007). | `jacksonJordan2008` | Preprint version of the published paper (*Combinatorica* 28 (2008), per the bib entry); no venue on the PDF. |
| `jackson-jordan-2008-pin-collinear-body-and-pin-frameworks.pdf` | B. Jackson, T. Jordán, Pin-collinear body-and-pin frameworks and the molecular conjecture, *Discrete Comput. Geom.* 40 (2008) 258–278, DOI 10.1007/s00454-008-9100-z. | `jacksonJordan2008pin` | The published version of the 2006 TR, renumbered: §§1–6, and its text has no rod-and-pin framework (the TR's §5 and Theorem 7.1). Printed pages start at 258 (pdf page = p. − 257). |
| `jackson-jordan-2010-generic-rank-of-body-bar.pdf` | B. Jackson, T. Jordán, The generic rank of body–bar-and-hinge frameworks, *European J. Combin.* 31 (2010) 574–588. | `jacksonJordan2009` | Published 2010; the bib key says 2009 (online year). Text layer has no word spaces. Printed pages start at 574. |
| `jacobs-1998-generic-rigidity-bond-bending-networks.pdf` | D. J. Jacobs, Generic rigidity in three-dimensional bond-bending networks, *J. Phys. A: Math. Gen.* 31 (1998) 6653–6668. | `jacobs1998` | Printed pages start at 6653 (pdf page = p. − 6652). Renamed from the publisher's `a83111.pdf`. |
| `jacobs-hendrickson-1997-rigidity-percolation-pebble-game.pdf` | D. J. Jacobs, B. Hendrickson, An algorithm for two-dimensional rigidity percolation: the pebble game, *J. Comput. Phys.* 137 (1997) 346–365. | `jacobsHendrickson1997` | Printed pages start at 346 (pdf page = p. − 345). |
| `jordan-2016-msj-memoirs.pdf` | T. Jordán, Combinatorial Rigidity: Graphs and Matroids in the Theory of Rigid Frameworks, in *Discrete Geometric Analysis*, MSJ Memoirs 34 (2016), pp. 33–112. | `jordan2016` | Printed pages start at 33 (pdf page = p. − 32). |
| `jordan-2023-rigid-block-and-hole-graphs-single-block.pdf` | T. Jordán, Rigid block and hole graphs with a single block, *Discrete Math.* 346 (2023) 113268, DOI 10.1016/j.disc.2022.113268. | — | Open access (CC BY-NC-ND). An article number, no running page numbers: 7 pdf pages, cite by theorem. Cited in `notes/Origami.md` (the single-block rank formula, Theorem 2.4). Renamed from the publisher's `1-s2.0-S0012365X22004745-main.pdf`. |
| `jordan-tanigawa-2022-globally-rigid-powers-of-graphs.pdf` | T. Jordán, S. Tanigawa, Globally rigid powers of graphs, *J. Combin. Theory Ser. B* 155 (2022) 111–140, DOI 10.1016/j.jctb.2022.02.004. | — | Open access. DOI from Crossref. Printed pages start at 111 (pdf page = p. − 110). Renamed from the publisher's `1-s2.0-S0095895622000120-main.pdf`. |
| `katoh-tanigawa-2009-molecular-conjecture-arxiv.pdf` | N. Katoh, S. Tanigawa, A proof of the molecular conjecture, arXiv:0902.0236v2 [math.CO] (12 Jul 2009). | `katohTanigawa2011` | arXiv version; numbering differs from the published paper, so cite the 2011 file for page numbers. |
| `katoh-tanigawa-2011-molecular-conjecture.pdf` | N. Katoh, S. Tanigawa, A proof of the molecular conjecture, *Discrete Comput. Geom.* 45 (2011) 647–700, DOI 10.1007/s00454-011-9348-6. | `katohTanigawa2011` | Printed pages start at 647 (pdf page = p. − 646). |
| `laman-1970-graphs-rigidity-plane-skeletal-structures.pdf` | G. Laman, On graphs and rigidity of plane skeletal structures, *J. Engrg. Math.* 4 (4) (Oct. 1970) 331–340. | `laman1970` | Printed pages start at 331 (pdf page = p. − 330). The OCR text layer garbles symbols. |
| `lee-streinu-2008-pebble-game-k-l-sparse.pdf` | A. Lee, I. Streinu, Pebble game algorithms and sparse graphs, *Discrete Math.* 308 (2008) 1425–1437, doi:10.1016/j.disc.2007.07.104. | `leeStreinu2008` | Printed pages start at 1425. |
| `lee-streinu-theran-2005-finding-maintaining-rigid.pdf` | A. Lee, I. Streinu, L. Theran, Finding and maintaining rigid components (4 pp.). | `leeStreinuTheran2005` | Venue is not printed on the PDF; the bib entry gives CCCG '05 (2005), and its reference list cites 2005 papers. Renamed from `-2008-`. |
| `lovasz-1977-flats-in-matroids-geometric-graphs.pdf` | L. Lovász, Flats in matroids and geometric graphs, in P. J. Cameron (ed.), *Combinatorial Surveys: Proceedings of the Sixth British Combinatorial Conference*, Academic Press, London, 1977, pp. 45–86. | — | The whole volume (246 pdf pages, scan with an OCR text layer); the paper is pdf pp. 57–98 (pdf page = p. + 12). |
| `lovasz-1989-singular-spaces-of-matrices.pdf` | L. Lovász, Singular spaces of matrices and their application in combinatorics, *Bol. Soc. Brasil. Mat.* 20 (1) (1989) 87–99. | — | Scan with a poor OCR text layer; the DOI 10.1007/BF02585470 is cited in `notes/Strata.md`, not printed on the PDF. |
| `lovasz-yemini-1982-on-generic-rigidity-in-the-plane.pdf` | L. Lovász, Y. Yemini, On generic rigidity in the plane, *SIAM J. Algebraic Discrete Methods* 3 (1) (Mar. 1982) 91–98. | — | Printed pages start at 91 (pdf page = p. − 90). |
| `lundqvist-stokes-ohman-2025-planar-rod-configuration-infinitesimally-rigid.pdf` | S. Lundqvist, K. Stokes, L.-D. Öhman, When is a planar rod configuration infinitesimally rigid?, *Discrete Comput. Geom.* 73 (1) (2025) 25–48, DOI 10.1007/s00454-023-00617-7. | — | The Online First copy (open access, © 2023), with no volume or page numbers printed; volume, issue and pages are from Crossref. Renamed from `When-is-a-Planar-Rod-Configuration-Infinitesimally-Rigid.pdf`. |
| `mackworth-1973-interpreting-pictures-polyhedral-scenes.pdf` | A. K. Mackworth, Interpreting pictures of polyhedral scenes, *Artificial Intelligence* 4 (1973) 121–137. | — | Printed pages start at 121 (pdf page = p. − 120). |
| `maxwell-1864-calculation-equilibrium-stiffness-of-frames.pdf` | J. C. Maxwell, On the calculation of the equilibrium and stiffness of frames, *Phil. Mag.* 27 (182) (1864) 294–299. | `maxwell1864` | Printed pages start at 294 (pdf page = p. − 293); p. 299 also carries the start of the next item. |
| `maxwell-1864-reciprocal-figures-diagrams-of-forces.pdf` | J. C. Maxwell, On reciprocal figures and diagrams of forces, *Phil. Mag.* 27 (182) (1864) 250–261, DOI 10.1080/14786446408643663. | — | Not the key `maxwell1864`, which is the stiffness paper. Issue and DOI from Crossref. Printed pages start at 250 (pdf page = p. − 249); pp. 250 and 261 share the page with the neighbouring items. |
| `maxwell-1870-reciprocal-figures-frames-diagrams-of-forces.pdf` | J. C. Maxwell, On reciprocal figures, frames, and diagrams of forces, *Trans. Roy. Soc. Edinburgh* 26 (1870) 1–40, DOI 10.1017/S0080456800026351. | — | pdf page 1 is a Cambridge cover sheet, so pdf page = p. + 1; Plates I–III are pdf pages 42–44. |
| `mnev-1988-universality-theorems-configuration-varieties.pdf` | N. E. Mnëv, The universality theorems on the classification problem of configuration varieties and convex polytopes varieties, pp. 527–543 of an edited volume (the text says "see his article in this volume"). | — | Volume title, series and editors are not printed on the PDF; printed pages start at 527 (pdf page = p. − 526). The Rohlin-seminar volume, *Lecture Notes in Math.* 1346, is the usual citation but is not shown here. |
| `nash-williams-1961-edge-disjoint-spanning-trees.pdf` | C. St. J. A. Nash-Williams, Edge-disjoint spanning trees of finite graphs, *J. London Math. Soc.* 36 (1961) 445–450. | `nashWilliams1961` | Printed pages start at 445. |
| `nash-williams-1964-decomposition-graphs-into-forests.pdf` | C. St. J. A. Nash-Williams, Decomposition of finite graphs into forests, *J. London Math. Soc.* 39 (1964) 12. | `nashWilliams1964` | One page; the bib entry gives the volume as s1-39. |
| `nixon-ross-2013-inductive-constructions-survey.pdf` | A. Nixon, E. Ross, One brick at a time: a survey of inductive constructions in rigidity theory, arXiv:1203.6623v2 [math.MG] (17 Jun 2013). | — | arXiv preprint; no venue on the PDF. |
| `oxley-2011-matroid-theory.pdf` | J. G. Oxley, *Matroid Theory*, 2nd ed., Oxford Graduate Texts in Mathematics 21, Oxford University Press, 2011. | `oxley2011` | Whole book, 719 pdf pages; edition and press come from the bib entry (the front matter lists the series). |
| `pollaczek-geiringer-1927-uber-die-gliederung-ebener-fachwerke.pdf` | H. Pollaczek-Geiringer, Über die Gliederung ebener Fachwerke, *Z. angew. Math. Mech.* 7 (1) (Feb. 1927), pp. 58–72 per the bib entry. | `pollaczekGeiringer1927` | Scan with a garbled text layer: read page images. The page after the title is p. 59 (pdf page = p. − 57). |
| `rybnikov-1999-stresses-and-liftings-cell-complexes.pdf` | K. Rybnikov, Stresses and liftings of cell-complexes, *Discrete Comput. Geom.* 21 (1999) 481–517. | — | Printed pages start at 481 (pdf page = p. − 480). |
| `schrijver-2004-combinatorial-optimization.pdf` | A. Schrijver, *Combinatorial Optimization: Polyhedra and Efficiency*, Algorithms and Combinatorics 24, Springer, 2003–2004 (three volumes in one file). | — | 1951 pdf pages; matroid material is in Vol. B. The copyright page gives ISBN 3-540-44389-4 (print edition); the year is not checked against it. |
| `servatius-1995-combinatorics-rigidity-siam.pdf` | B. Servatius, Combinatorics and the rigidity of frameworks (6 pp.). | — | Venue and year are not printed on the PDF (the filename's "siam" is unverified); its reference list cites works to 1989. |
| `streinu-theran-2009-sparse-hypergraphs-pebble.pdf` | I. Streinu, L. Theran, Sparse hypergraphs and pebble game algorithms, *European J. Combin.* 30 (2009) 1944–1964. | — | Text layer has no word spaces. Printed pages start at 1944. |
| `sugihara-1983-unifying-approach-descriptive-geometry-mechanisms.pdf` | K. Sugihara, A unifying approach to descriptive geometry and mechanisms, *Discrete Appl. Math.* 5 (1983) 313–328. | — | Printed pages start at 313 (pdf page = p. − 312). |
| `sugihara-1984-algebraic-combinatorial-approach-line-drawings.pdf` | K. Sugihara, An algebraic and combinatorial approach to the analysis of line drawings of polyhedra, *Discrete Appl. Math.* 9 (1984) 77–104. | `sugihara1984` | Printed pages start at 77 (pdf page = p. − 76). |
| `sugihara-1986-machine-interpretation-of-line-drawings.pdf` | K. Sugihara, *Machine Interpretation of Line Drawings*, MIT Press, 1986. | — | The author's free web version, re-typeset in LaTeX (preface dated September 2006), so its page numbers differ from the print edition: cite by section. Its p. 1 is pdf page 8 (pdf page = p. + 7). Renamed from `mild.pdf`. |
| `tanigawa-2010-generic-rigidity-matroids-with-dilworth-truncations.pdf` | S. Tanigawa, Generic rigidity matroids with Dilworth truncations, arXiv:1010.5699v2 [math.CO] (25 Apr 2012). | — | arXiv preprint; no venue on the PDF. |
| `tay-1984-rigidity-multi-graphs-i.pdf` | T.-S. Tay, Rigidity of multi-graphs. I. Linking rigid bodies in n-space, *J. Combin. Theory Ser. B* 36 (1984) 95–112. | `tay1984` | Printed pages start at 95. |
| `tay-1989-linking-n-2-panels-ii.pdf` | T.-S. Tay, Linking (n−2)-dimensional panels in n-space II: (n−2,2)-frameworks and body and hinge structures, *Graphs Combin.* 5 (1989) 245–273. | `tay1989` | Printed pages start at 245. |
| `tay-whiteley-1984-recent-advances-generic-rigidity.pdf` | T.-S. Tay, W. Whiteley, Recent advances in the generic rigidity of structures, *Structural Topology* 9 (1984) 31–38. | `tayWhiteley1984` | Scan with no text layer (read it as page images); pages are stored rotated 90°. Bilingual, French and English in parallel columns; printed pages start at 31 (pdf page = p. − 30). The printed title reads "Ridigity" (sic). Renamed from UPCommons' `st9-06-a3.pdf` (https://hdl.handle.net/2099/1017). |
| `tay-whiteley-1985-generating-isostatic.pdf` | T.-S. Tay, W. Whiteley, Generating isostatic frameworks, *Structural Topology* 11 (1985) 21–69. | `tayWhiteley1985` | Bilingual (French then English); printed pages start at 21 (pdf page = p. − 20). The page range is from the bib entry; the title page shows only "#11, 1985". |
| `tutte-1961-decomposing-connected-factors.pdf` | W. T. Tutte, On the problem of decomposing a graph into n connected factors, *J. London Math. Soc.* 36 (1961) 221–230. | `tutte1961` | Printed pages start at 221. |
| `white-1994-grassmann-cayley.pdf` | N. L. White, Grassmann–Cayley algebra and robotics, *J. Intelligent Robotic Systems* 11 (1994) 91–107. | `white1994` | Printed pages start at 91. |
| `white-whiteley-1983-algebraic-geometry-of-stresses.pdf` | N. L. White, W. Whiteley, The algebraic geometry of stresses in frameworks, *SIAM J. Algebraic Discrete Methods* 4 (4) (Dec. 1983) 481–511, DOI 10.1137/0604049. | — | pdf page 1 is a ResearchGate cover sheet; printed pages start at 481 on pdf page 2 (pdf page = p. − 479). |
| `white-whiteley-1987-algebraic-geometry-of-motions.pdf` | N. L. White, W. Whiteley, The algebraic geometry of motions of bar-and-body frameworks, *SIAM J. Algebraic Discrete Methods* 8 (1) (Jan. 1987) 1–32. | `whiteWhiteley1987` | Printed pages start at 1. |
| `whiteley-1982-motions-stresses-projected-polyhedra.pdf` | W. Whiteley, Motions and stresses of projected polyhedra, *Structural Topology* 7 (1982) 13–38. | — | Scan, no text layer: read with the Read tool's `pages`. Bilingual (French then English); printed pages start at 13 (pdf page = p. − 12). Renamed from `st7-05-a2.pdf`. |
| `whiteley-1984-scene-analysis-motions-frameworks.pdf` | W. Whiteley, A correspondence between scene analysis and motions of frameworks, *Discrete Appl. Math.* 9 (1984) 269–295, PII 0166-218X(84)90027-1. | `whiteley1984` | Printed pages start at 269 (pdf page = p. − 268). Renamed from the publisher's `1-s2.0-0166218X84900271-main.pdf`. |
| `whiteley-1987-rigidity-and-polarity-i.pdf` | W. Whiteley, Rigidity and polarity I: statics of sheet structures, *Geom. Dedicata* 22 (1987) 329–362, DOI 10.1007/BF00147940. | — | Journal line printed on p. 329 only; DOI from Crossref. Printed pages start at 329 (pdf page = p. − 328). |
| `whiteley-1988-union-of-matroids.pdf` | W. Whiteley, The union of matroids and the rigidity of frameworks, *SIAM J. Discrete Math.* 1 (2) (May 1988) 237–255. | `whiteley1988` | Printed pages start at 237 (pdf page = p. − 236). |
| `whiteley-1989-matroid-on-hypergraphs.pdf` | W. Whiteley, A matroid on hypergraphs, with applications in scene analysis and geometry, *Discrete Comput. Geom.* 4 (1989) 75–95. | `whiteley1989` | Printed pages start at 75 (pdf page = p. − 74). Renamed from the publisher's `BF02187716.pdf`. |
| `whiteley-1989-rigidity-and-polarity-ii.pdf` | W. Whiteley, Rigidity and polarity II: weaving lines and tensegrity frameworks, *Geom. Dedicata* 30 (1989) 255–279, DOI 10.1007/BF00181341. | — | Journal line printed on p. 255 only; DOI from Crossref. Printed pages start at 255 (pdf page = p. − 254). |
| `whiteley-1991-weavings-sections-projections-spherical-polyhedra.pdf` | W. Whiteley, Weavings, sections and projections of spherical polyhedra, *Discrete Appl. Math.* 32 (1991) 275–294, PII 0166-218X(91)90004-G. | — | Volume 32 is printed on p. 275 (Crapo–Whiteley 1993's bibliography says 33). Scan with an OCR text layer: formulas are garbled and Theorem 3.7 reads "3.1". Printed pages start at 275 (pdf page = p. − 274). Renamed from `whiteley1991-dam32-275.pdf`. |
| `whiteley-1996-matroids-discrete-geometry.pdf` | W. Whiteley, Some matroids from discrete applied geometry (dated 6 June 1996; "Contemporary Mathematics, Volume 00, 0000" template). | `whiteley1996` | Author's preprint (140 pages) of the *Contemporary Math.* 197 (1996) 171–311 paper per the bib entry; its page numbers differ from the published ones. |
| `whiteley-1999-rigidity-of-molecular-structures-generic-and-geometric-analysis.pdf` | W. Whiteley, Rigidity of molecular structures: generic and geometric analysis, in *Rigidity Theory and Applications*, ed. Thorpe and Duxbury, Kluwer Academic/Plenum, 1999. | `whiteley1999` | Pages 21–46, as the bib entry says: the text layer has "21" at the foot of pdf page 1 (pdf page = p. − 20). Bib title says "geometric and generic". |
| `whiteley-2005-counting-flexibility-molecules.pdf` | W. Whiteley, Counting out to the flexibility of molecules, *Phys. Biol.* 2 (2005) S116–S126, doi:10.1088/1478-3975/2/4/S06. | — | IOPscience download copy; printed pages start at S116. |
| `zheng-2026-stress-degeneracy-direction-complexes.pdf` | D. Zheng, Stress degeneracy of direction complexes of (2,2)-sparse graphs and three-dimensional body–pin rigidity (preprint, August 2026). | — | Unrefereed preprint; running header reads "Stress Degeneracy for Sparse-Graph Direction Complexes Preprint". Renamed from `zheng-2026-body_pin_partition_collinearity_flag_en_20260816.pdf` (the 20260816 suffix was a date stamp). |

For formal `\cite{}` work in the blueprint, see `blueprint/AUTHORING.md`
*Citations* (bib-entry conventions) and `blueprint/CLAUDE.md` *Static checks
before commit*.
