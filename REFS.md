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

## Catalogue of `.refs/`

`.refs/` is gitignored, so a fresh clone has none of these PDFs; this table lists what the main checkout holds, one row per file. New PDFs follow the naming convention `<surnames>-<year>-<short-title-slug>.pdf` (lowercase ASCII, hyphens, first-author surname or up to three surnames, the publication year, 3–6 title words, a `-tr` suffix for a technical-report version). "Bib key" is the entry in `blueprint/src/bibliography.bib`, if any.

| File | Reference | Bib key | Notes |
|---|---|---|---|
| `barnabei-brini-rota-1985-on-the-exterior-calculus.pdf` | M. Barnabei, A. Brini, G.-C. Rota, On the exterior calculus of invariant theory, *J. Algebra* 96 (1985) 120–160. | `barnabeiBriniRota1985` | Printed pages start at 120. |
| `chen-cruickshank-kitson-2023-block-and-hole.pdf` | B. G. Chen, J. Cruickshank, D. Kitson, Block-and-hole graphs: constructibility and (3,0)-sparsity, arXiv:2309.06804v1 [math.CO] (13 Sep 2023). | — | arXiv preprint; no venue on the PDF. |
| `crapo-whiteley-1982-statics-of-frameworks.pdf` | H. Crapo, W. Whiteley, Statics of frameworks and motions of panel structures, a projective geometric introduction, *Structural Topology* 6 (1982) 43–82. | `crapoWhiteley1982` | Bilingual (French then English); printed pages start at 43 (pdf page = p. − 42). |
| `doubilet-rota-stein-1974-on-the-foundations-of-combinatorial-theory-ix.pdf` | P. Doubilet, G.-C. Rota, J. Stein, On the foundations of combinatorial theory: IX, Combinatorial methods in invariant theory, *Studies in Applied Mathematics* 53 (3) (Sept. 1974); the paper starts at p. 185 per its contents page. | — | Printed pages start at 185 (pdf page = p. − 184). |
| `edmonds-1965-minimum-partition-matroid.pdf` | J. Edmonds, Minimum partition of a matroid into independent subsets, *J. Res. Nat. Bur. Standards Sect. B* 69B (1–2) (Jan.–June 1965) 67–72. | `edmonds1965` | Printed pages start at 67 (pdf page = p. − 66); the running text OCR has spurious spaces. |
| `finbow-ross-whiteley-2009-rigidity-of-spherical-frameworks.pdf` | W. Finbow, E. Ross, W. Whiteley, The rigidity of spherical frameworks: swapping blocks and holes (preprint, compiled 21 Oct 2018). | — | Preprint; no venue, volume or pages on the PDF. |
| `jackson-jordan-2006-pin-collinear-tr.pdf` | B. Jackson, T. Jordán, Pin-collinear body-and-pin frameworks and the molecular conjecture, EGRES Technical Report TR-2006-06 (31 Aug 2006). | `jacksonJordan2008pin` | Tech-report version of the published paper (*Discrete Comput. Geom.* 40 (2008), per the bib entry). |
| `jackson-jordan-2008-on-the-rigidity-of-molecular-graphs.pdf` | B. Jackson, T. Jordán, On the rigidity of molecular graphs (preprint dated 16 Nov 2007). | `jacksonJordan2008` | Preprint version of the published paper (*Combinatorica* 28 (2008), per the bib entry); no venue on the PDF. |
| `jackson-jordan-2010-generic-rank-of-body-bar.pdf` | B. Jackson, T. Jordán, The generic rank of body–bar-and-hinge frameworks, *European J. Combin.* 31 (2010) 574–588. | `jacksonJordan2009` | Published 2010; the bib key says 2009 (online year). Text layer has no word spaces. Printed pages start at 574. |
| `jordan-2016-msj-memoirs.pdf` | T. Jordán, Combinatorial Rigidity: Graphs and Matroids in the Theory of Rigid Frameworks, in *Discrete Geometric Analysis*, MSJ Memoirs 34 (2016), pp. 33–112. | `jordan2016` | Printed pages start at 33 (pdf page = p. − 32). |
| `katoh-tanigawa-2009-molecular-conjecture-arxiv.pdf` | N. Katoh, S. Tanigawa, A proof of the molecular conjecture, arXiv:0902.0236v2 [math.CO] (12 Jul 2009). | `katohTanigawa2011` | arXiv version; numbering differs from the published paper, so cite the 2011 file for page numbers. |
| `katoh-tanigawa-2011-molecular-conjecture.pdf` | N. Katoh, S. Tanigawa, A proof of the molecular conjecture, *Discrete Comput. Geom.* 45 (2011) 647–700, DOI 10.1007/s00454-011-9348-6. | `katohTanigawa2011` | Printed pages start at 647 (pdf page = p. − 646). |
| `lee-streinu-2008-pebble-game-k-l-sparse.pdf` | A. Lee, I. Streinu, Pebble game algorithms and sparse graphs, *Discrete Math.* 308 (2008) 1425–1437, doi:10.1016/j.disc.2007.07.104. | `leeStreinu2008` | Printed pages start at 1425. |
| `lee-streinu-theran-2005-finding-maintaining-rigid.pdf` | A. Lee, I. Streinu, L. Theran, Finding and maintaining rigid components (4 pp.). | `leeStreinuTheran2005` | Venue is not printed on the PDF; the bib entry gives CCCG '05 (2005), and its reference list cites 2005 papers. Renamed from `-2008-`. |
| `lovasz-1989-singular-spaces-of-matrices.pdf` | L. Lovász, Singular spaces of matrices and their application in combinatorics, *Bol. Soc. Brasil. Mat.* 20 (1) (1989) 87–99. | — | Scan with a poor OCR text layer; the DOI 10.1007/BF02585470 is cited in `notes/Strata.md`, not printed on the PDF. |
| `lovasz-yemini-1982-on-generic-rigidity-in-the-plane.pdf` | L. Lovász, Y. Yemini, On generic rigidity in the plane, *SIAM J. Algebraic Discrete Methods* 3 (1) (Mar. 1982) 91–98. | — | Printed pages start at 91 (pdf page = p. − 90).
| `mnev-1988-universality-theorems-configuration-varieties.pdf` | N. E. Mnëv, The universality theorems on the classification problem of configuration varieties and convex polytopes varieties, pp. 527–543 of an edited volume (the text says "see his article in this volume"). | — | Volume title, series and editors are not printed on the PDF; printed pages start at 527 (pdf page = p. − 526). The Rohlin-seminar volume, *Lecture Notes in Math.* 1346, is the usual citation but is not shown here. |
| `nash-williams-1961-edge-disjoint-spanning-trees.pdf` | C. St. J. A. Nash-Williams, Edge-disjoint spanning trees of finite graphs, *J. London Math. Soc.* 36 (1961) 445–450. | `nashWilliams1961` | Printed pages start at 445. |
| `nixon-ross-2013-inductive-constructions-survey.pdf` | A. Nixon, E. Ross, One brick at a time: a survey of inductive constructions in rigidity theory, arXiv:1203.6623v2 [math.MG] (17 Jun 2013). | — | arXiv preprint; no venue on the PDF. |
| `oxley-2011-matroid-theory.pdf` | J. G. Oxley, *Matroid Theory*, 2nd ed., Oxford Graduate Texts in Mathematics 21, Oxford University Press, 2011. | `oxley2011` | Whole book, 719 pdf pages; edition and press come from the bib entry (the front matter lists the series). |
| `pollaczek-geiringer-1927-uber-die-gliederung-ebener-fachwerke.pdf` | H. Pollaczek-Geiringer, Über die Gliederung ebener Fachwerke, *Z. angew. Math. Mech.* 7 (1) (Feb. 1927), pp. 58–72 per the bib entry. | `pollaczekGeiringer1927` | Scan with a garbled text layer: read page images. The page after the title is p. 59 (pdf page = p. − 57). |
| `schrijver-2004-combinatorial-optimization.pdf` | A. Schrijver, *Combinatorial Optimization: Polyhedra and Efficiency*, Algorithms and Combinatorics 24, Springer, 2003–2004 (three volumes in one file). | — | 1951 pdf pages; matroid material is in Vol. B. The copyright page gives ISBN 3-540-44389-4 (print edition); the year is not checked against it. |
| `servatius-1995-combinatorics-rigidity-siam.pdf` | B. Servatius, Combinatorics and the rigidity of frameworks (6 pp.). | — | Venue and year are not printed on the PDF (the filename's "siam" is unverified); its reference list cites works to 1989. |
| `streinu-theran-2009-sparse-hypergraphs-pebble.pdf` | I. Streinu, L. Theran, Sparse hypergraphs and pebble game algorithms, *European J. Combin.* 30 (2009) 1944–1964. | — | Text layer has no word spaces. Printed pages start at 1944. |
| `tanigawa-2010-generic-rigidity-matroids-with-dilworth-truncations.pdf` | S. Tanigawa, Generic rigidity matroids with Dilworth truncations, arXiv:1010.5699v2 [math.CO] (25 Apr 2012). | — | arXiv preprint; no venue on the PDF. |
| `tay-1984-rigidity-multi-graphs-i.pdf` | T.-S. Tay, Rigidity of multi-graphs. I. Linking rigid bodies in n-space, *J. Combin. Theory Ser. B* 36 (1984) 95–112. | `tay1984` | Printed pages start at 95. |
| `tay-1989-linking-n-2-panels-ii.pdf` | T.-S. Tay, Linking (n−2)-dimensional panels in n-space II: (n−2,2)-frameworks and body and hinge structures, *Graphs Combin.* 5 (1989) 245–273. | `tay1989` | Printed pages start at 245. |
| `tay-whiteley-1985-generating-isostatic.pdf` | T.-S. Tay, W. Whiteley, Generating isostatic frameworks, *Structural Topology* 11 (1985) 21–69. | `tayWhiteley1985` | Bilingual (French then English); printed pages start at 21 (pdf page = p. − 20). The page range is from the bib entry; the title page shows only "#11, 1985". |
| `tutte-1961-decomposing-connected-factors.pdf` | W. T. Tutte, On the problem of decomposing a graph into n connected factors, *J. London Math. Soc.* 36 (1961) 221–230. | `tutte1961` | Printed pages start at 221. |
| `white-1994-grassmann-cayley.pdf` | N. L. White, Grassmann–Cayley algebra and robotics, *J. Intelligent Robotic Systems* 11 (1994) 91–107. | `white1994` | Printed pages start at 91. |
| `white-whiteley-1983-algebraic-geometry-of-stresses.pdf` | N. L. White, W. Whiteley, The algebraic geometry of stresses in frameworks, *SIAM J. Algebraic Discrete Methods* 4 (4) (Dec. 1983) 481–511, DOI 10.1137/0604049. | — | pdf page 1 is a ResearchGate cover sheet; printed pages start at 481 on pdf page 2 (pdf page = p. − 479). |
| `white-whiteley-1987-algebraic-geometry-of-motions.pdf` | N. L. White, W. Whiteley, The algebraic geometry of motions of bar-and-body frameworks, *SIAM J. Algebraic Discrete Methods* 8 (1) (Jan. 1987) 1–32. | `whiteWhiteley1987` | Printed pages start at 1. |
| `whiteley-1982-motions-stresses-projected-polyhedra.pdf` | W. Whiteley, Motions and stresses of projected polyhedra, *Structural Topology* 7 (1982) 13–38. | — | Scan, no text layer: read with the Read tool's `pages`. Bilingual (French then English); printed pages start at 13 (pdf page = p. − 12). Renamed from `st7-05-a2.pdf`. |
| `whiteley-1984-scene-analysis-motions-frameworks.pdf` | W. Whiteley, A correspondence between scene analysis and motions of frameworks, *Discrete Appl. Math.* 9 (1984) 269–295, PII 0166-218X(84)90027-1. | — | Printed pages start at 269 (pdf page = p. − 268). Renamed from the publisher's `1-s2.0-0166218X84900271-main.pdf`. |
| `whiteley-1988-union-of-matroids.pdf` | W. Whiteley, The union of matroids and the rigidity of frameworks, *SIAM J. Discrete Math.* 1 (2) (May 1988) 237–255. | `whiteley1988` | Printed pages start at 237 (pdf page = p. − 236). |
| `whiteley-1989-matroid-on-hypergraphs.pdf` | W. Whiteley, A matroid on hypergraphs, with applications in scene analysis and geometry, *Discrete Comput. Geom.* 4 (1989) 75–95. | — | Printed pages start at 75 (pdf page = p. − 74). Renamed from the publisher's `BF02187716.pdf`. |
| `whiteley-1996-matroids-discrete-geometry.pdf` | W. Whiteley, Some matroids from discrete applied geometry (dated 6 June 1996; "Contemporary Mathematics, Volume 00, 0000" template). | `whiteley1996` | Author's preprint (140 pages) of the *Contemporary Math.* 197 (1996) 171–311 paper per the bib entry; its page numbers differ from the published ones. |
| `whiteley-1999-rigidity-of-molecular-structures-generic-and-geometric-analysis.pdf` | W. Whiteley, Rigidity of molecular structures: generic and geometric analysis, in *Rigidity Theory and Applications*, ed. Thorpe and Duxbury, Kluwer Academic/Plenum, 1999. | `whiteley1999` | Pages 21–46 per the bib entry; the PDF carries no printed page numbers on page 1. Bib title says "geometric and generic". |
| `whiteley-2005-counting-flexibility-molecules.pdf` | W. Whiteley, Counting out to the flexibility of molecules, *Phys. Biol.* 2 (2005) S116–S126, doi:10.1088/1478-3975/2/4/S06. | — | IOPscience download copy; printed pages start at S116. |
| `zheng-2026-stress-degeneracy-direction-complexes.pdf` | D. Zheng, Stress degeneracy of direction complexes of (2,2)-sparse graphs and three-dimensional body–pin rigidity (preprint, August 2026). | — | Unrefereed preprint; running header reads "Stress Degeneracy for Sparse-Graph Direction Complexes Preprint". Renamed from `zheng-2026-body_pin_partition_collinearity_flag_en_20260816.pdf` (the 20260816 suffix was a date stamp). |

For formal `\cite{}` work in the blueprint, see `blueprint/AUTHORING.md`
*Citations* (bib-entry conventions) and `blueprint/CLAUDE.md` *Static checks
before commit*.
