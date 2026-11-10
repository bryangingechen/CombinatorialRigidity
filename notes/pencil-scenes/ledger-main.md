# PENCIL-SCENES recon: attribution ledger for `pencil.tex` and `main-component.tex`

*Banked as delivered by a read-only recon agent on 2026-11-09. The coordinator's spot-checks, and the
corrections they found, are in `notes/PencilScenes.md` §5; read that first.*

Read-only recon share, 2026-11-09. Scope: every node or prose passage of
`blueprint/src/chapter/pencil.tex` and `blueprint/src/chapter/main-component.tex` that
states or uses the classical scene-analysis material of `notes/PencilScenes.md` §3. The
combinatorial steps (cut vertices, ears, contractions, coverage, sparsity) are left out
unless their prose uses this material. `pencil-d.tex` and the questions Q1–Q4 are other
shares.

## Conventions

- **Pages are printed pages**, read from the PDFs in `.refs/` (pypdf in the blueprint venv;
  Whiteley 1982 is a scan, read as page images). Offsets: Crapo–Whiteley 1982, pdf = p. − 42;
  Whiteley 1982, pdf = p. − 12; Whiteley 1984, pdf = p. − 268; Whiteley 1989, pdf = p. − 74;
  Whiteley 1996 is the author's preprint (pdf page = preprint page; published pages differ);
  the Jackson–Jordán EGRES report TR-2006-06, pdf = p. + 1; Whiteley 1999, pdf = p. − 20;
  Katoh–Tanigawa 2011, pdf = p. − 646.
- **Short names.** CW82 = Crapo–Whiteley 1982 (`crapoWhiteley1982`); W82 = Whiteley, "Motions
  and stresses of projected polyhedra", *Structural Topology* 7 (1982) 13–38 (no bib key);
  W84 = Whiteley, "A correspondence between scene analysis and motions of frameworks",
  *Discrete Appl. Math.* 9 (1984) 269–295 (no bib key); W89 = Whiteley, "A matroid on
  hypergraphs, with applications in scene analysis and geometry", *Discrete Comput. Geom.* 4
  (1989) 75–95 (no bib key); W96 = `whiteley1996` (preprint); W99 = `whiteley1999`;
  JJ = Jackson–Jordán, `jacksonJordan2008pin`, read in the 2006 report (**theorem numbers
  are the report's; the published numbering is unverified**); KT = `katohTanigawa2011`.
- **S_G** is the incidence structure with points V(G), faces V(G), and w on face v iff
  w ∈ N[v]. It is symmetric, so S_G is its own dual (W96 Remark 8.3.2 swaps points and faces).
- **Status** is what the node (statement and proof) or the passage says now: *cited*, *partly
  cited*, *uncited*, or *presented as new* (framed as the project's own idea with no lineage).

## The bridge (derived from the chapters' definitions, not from a source)

These identifications organize the rows. They follow from the chapter definitions; no source
in `.refs/` states them for S_G.

1. **Pencil realizations are realizations of S_G.** If a pencil realization has nonzero hinges
   and adjacent points independent, the hinge of uv spans ⟨q_u, q_v⟩ and lies in both panels,
   so q_w lies on the plane n_v for every w ∈ N[v]. Conversely, points and planes realizing
   S_G with adjacent points distinct give a pencil realization with hinge q_u ∨ q_v.
2. **A configuration (q, z) with z ∈ L(q) is a scene of S_G over q** in W84's sense
   (Definitions 2.1–2.2, p. 272): affine points over the picture, non-vertical face planes.
   `def:pencil-lifting-system` is W84's scene matrix A for S_G (p. 272), up to the sign of
   the plane coefficients.
3. **F(q) is the face-plane projection of the scene space, and the motion space of W84's
   reduced plate framework L(S_G(q)).** Ordering the faces at each vertex w with w's own face
   first, W84's row reduction (p. 282) gives for each w a fan of bars along the line
   (x_w, y_w, 1) from plate w to each neighbour's plate. Adjacent plates u, w then get two
   bars, on the lines (x_u, y_u, 1) and (x_w, y_w, 1), which act as one pin at their meet.
   That is P_q (`lem:pencil-lifting-planes-motions`), and its motion equations are exactly
   F(q)'s. Other reduction orders give line-equivalent frameworks (W84 p. 283, Prop. 4.3).
4. **P_q is JJ's rod-and-pin framework (G, p) with p(v) = −q_v.** JJ's pin-line of v is
   {p_1(v) x + p_2(v) y = 1} and the pin of uv is L_u ∩ L_v (JJ §5, p. 12). The line with
   coordinates (x_v, y_v, 1) is that pin-line at p(v) = −q_v. JJ's "generic rod-and-pin
   framework" is P_q at a generic picture.

## Ledger: `blueprint/src/chapter/pencil.tex`

| # | Label or passage | What it claims | Classical source (checked) | Status | Discrepancy |
|---|---|---|---|---|---|
| P1 | `sec:pencil` intro (lines 35–38): "builds pencil realizations by lifting pictures of $G$ in the plane" | The main component is built by lifting plane pictures. | The lifting of plane pictures: W84 Defs 2.1–2.3 (pp. 272–273); W82 p. 14. | uncited | No word that this is scene analysis. |
| P2 | `sec:pencil-roadmap`, Part B (lines 67–70) and "The main-component induction" (lines 96–101): "lift it to a point of $K^4$ by a height … $L(q)$, the lifting space" | Place bodies at a picture, lift by heights; a pencil realization iff the heights lie in L(q). | Scenes of S_G over q (bridge 1–2): W84 Defs 2.1–2.2 (p. 272); heights-only form W89 Def. 2.2 and the line after it (pp. 77–78); W96 §8.3 (pp. 44–45). | presented as new | Framed as "Our proof has three parts"; nothing says the carrier is classical. Holds over every field, where W84 and W89 work over the reals. |
| P3 | `sec:pencil-roadmap` (lines 101–103): "In dimension $d$ a configuration has $d - 2$ heights, each in $L(q)$" | d − 2 independent scenes over one picture. | None found. W84 §7.2 (p. 292) treats K-space pictures with hyperplane faces. Its Remark (p. 292) says plane pictures of 4-dimensional scenes with hyperplane faces give non-linear equations. | uncited | The construction itself belongs to the `pencil-d.tex` share. The d − 2 heights stay linear because the faces are 2-planes (each height affine on N[v] separately), not hyperplanes. That is the contrast with W84's Remark. |
| P4 | `sec:pencil-roadmap`, equal deficiencies (lines 141–150): "This rests on Jackson and Jordán's equality for $\dim L(q)$ \cite{jacksonJordan2008pin}" | The flat configuration attains over a main picture when def₂ = def_d, by JJ's equality, derived from KT 5.6. | JJ Theorem 7.1 (p. 21) with the rod-and-pin framework of §5 (p. 12) (bridge 4). Flat motions = scenes: W84 §5.1–5.3 (pp. 287–289). | partly cited | JJ is cited, but without an item number, and JJ state nothing about L(q). The reading of dim L(q) as a scene dimension needs W84 Prop. 4.1 (bridge 3), which is unsaid. W89 Thm 5.4 (the independent case) is unsaid. |
| P5 | `sec:pencil-roadmap`, "The heights recover a gap" (lines 233–240) | The flat rank is D(\|V\|−1)+3−dim L(q), and dim L(q) = 3+def₂ at a main picture. | Flat motions ≅ scenes: W84 §5.1–5.3 (pp. 287–289), which credits W82 for the observation (p. 289, ref. [18]); W82 p. 14. | uncited | Cross-references only. The rank count in the screw space is the project's. |
| P6 | `sec:pencil-roadmap`, "Bodies of degree two" (lines 242–250): "imposes no condition on the heights … the conditions that cut out $L(q)$ sit at the pencil hubs" | A face with three points imposes no condition on the heights. | W89 Def. 3.2 (pp. 82–83): a face with fewer than four vertices contributes no edge to the derived 4-hypergraph H(S). | uncited | Elementary; optional citation. |
| P7 | `sec:pencil-roadmap`, "A planar-rigid set acts as one body" (lines 251–259): "over a main picture the points of $W$ lie in one plane" | Rigid sub-structure ⇒ flat sub-scene. | W84 Cor. 4.2(i) (p. 283): flat picture iff rigid reduced framework, applied to S_{G[W]}. W89 Cor. 3.2, proof of (a)⇒(b) (p. 85): a tight sub-count forces its faces into a common plane over a general picture. | uncited | The extension from a generic picture to every main picture is the project's (`rem:pencil-x0-flatness`). |
| P8 | `sec:pencil-main-component-route` (lines 956–990): "The idea of \cref{sec:main-component} is to build pencil realizations by lifting planar pictures" | Lifted configurations, L(q), and the vector bundle over the main pictures. | As P2. Main picture ↔ W84 Def. 2.4 (p. 273), the generic degree of freedom. | presented as new | No lineage anywhere in the subsection. |
| P9 | `sec:pencil-duality` intro (lines 350–358), `lem:pencil-transport-through-to-in`, `lem:pencil-transport-in-to-through` | The polarity turns "passes through q" into "lies in the panel with normal q", and back. | Point ↔ plane polarity exchanging hinge-concurrent and panel-hinge frameworks: KT p. 650; W99 pp. 21 (item (c)) and 29–30; JJ report footnote 2 (p. 2). Correlations on the screw space: CW82 §3.6. | partly cited | Nothing in `pencil.tex` cites these. The lemmas use `lem:polarity-join`, whose chapter (`molecule-modelling.tex`) cites CW82 §3.6, KT §5.1 and pp. 650, 671, and W99 Cor. 12. |
| P10 | `lem:pencil-self-dual` and the remark after it (lines 413–445) | The polarity takes a pencil realization (F, n, q) to one with normals and points exchanged. | No source found states this. By bridge 1 it is the self-duality S_G = S_G* acting on realizations of S_G in P³. | uncited | **Not** W96 Remark 8.3.2 (see the corrections to §3 below). The underlying duality is classical (P9); the self-duality of the pencil class appears to be the project's. |
| P11 | `sec:pencil-realization` (line 318): "This is the classical picture of a pencil of lines through a point in a plane." | The term "pencil". | Standard projective geometry (a flat pencil of lines); not scene analysis. | uncited | Outside the scene scope. Under the citation bar, "classical" without a pointer is acceptable only as the bare word. |

## Ledger: `blueprint/src/chapter/main-component.tex`

| # | Label or passage | What it claims | Classical source (checked) | Status | Discrepancy |
|---|---|---|---|---|---|
| M1 | `sec:main-component` intro (lines 1–10, 102–109): "the idea of this section, to lift planar pictures"; "derives Jackson and Jordán's equality \cite{jacksonJordan2008pin} for the dimension of the lifting space" | The section's method, and JJ's equality as a statement about dim L(q). | JJ Theorem 7.1 (p. 21) and §5 (p. 12). Scenes: W84. | partly cited | **Mild misattribution.** JJ prove a rank formula for rod-and-pin frameworks and never mention L(q), scenes or liftings (a keyword search of the report finds only reference titles). "For the dimension of the lifting space" needs the uncited W84 bridge (bridge 3). |
| M2 | Notation list (lines 33–49): $L_G(q)$, the "pencil configuration space", the "main component" | Names. | Space of scenes over a picture: W84 Def. 2.4 (p. 273). | uncited | Minor. |
| M3 | `sec:main-component-carrier` intro (lines 156–177): "as in scene analysis … In the language of scene analysis, $L(q)$ is the space of heights of the liftings of $q$ … trivial liftings, which put all the faces in one plane (see Whiteley \cite{whiteley1996}, \S 8.3)" | L(q) is the space of heights of liftings of q for S_G; Aff(q) are the trivial liftings. | W96 §8.3 (pp. 44–45) has "lifting" and "trivial if all the faces lie in the same plane" (verified). Primary: W84 Defs 2.1–2.3 (pp. 272–273). The heights-only form is W89 p. 78. W84 p. 271 calls these "the standard linear equations for polyhedral scenes", crediting Duda–Hart 1975 and Sugihara. | partly cited | W96 is a survey, so under the citation bar it should be cited only as the presentation followed, beside a primary source. This passage is the only scene-analysis citation in the two files. |
| M4 | `def:pencil-admissible-picture` | Adjacent points distinct; no closed neighbourhood collinear. | Admissibility is the condition under which heights determine face planes: W89 Thm 3.1 proof (p. 84) assumes faces with ≥ 3 vertices and a general picture with "no three points on a line". W84 assumes non-vertical faces (p. 271). | uncited | Minor. Here non-verticality is derived (`lem:pencil-condition-linear`), not assumed. |
| M5 | `def:pencil-lifting-space` (L(q), Aff(q)) | Heights affine on every closed neighbourhood. | Scenes over a picture, heights-only: W89 Def. 2.2 and the line after it (pp. 77–78), for 4-uniform hypergraphs; general incidence structures: W84 Def. 2.1 (p. 272), W89 Def. 3.1 (p. 82). | uncited at the node (M3's prose cites W96) | W84 and W89 work over ℝ; the definition here is over every field, which is harmless (it is linear). |
| M6 | `lem:pencil-lifting-space-affine` | Aff(q) ⊆ L(q), of dimension 3 at an admissible picture. | W89 p. 78: "Any picture will have the trivial scenes, with all vertices coplanar. Unless the vertices in the picture are collinear, these trivial scenes form a three-dimensional subspace." (exact match). W84 p. 272 (trivial scenes in (z, r)-space). | partly cited (M3's prose names the trivial liftings, citing W96) | None. |
| M7 | `lem:pencil-condition-linear` | Coplanarity of each N[v] ⟺ z ∈ L(q); the plane is non-vertical. | Linearity of the scene equations: W84 eq. (1) (p. 272); W89 p. 78 (one determinant per 4 points). | uncited | Classical in substance. The non-vertical-plane derivation from admissibility is the project's. |
| M8 | `def:pencil-lifting-system` (M(q)) | The system z_w = h_v·(x_w, y_w, 1) for w ∈ N[v], with dim of solutions = dim L(q) at an admissible picture. | It is W84's scene matrix A (p. 272), W89's A(S, p) (Def. 3.1, p. 82), W96's "lifting matrix M(S, r)" (§8.3, pp. 44–45). Solutions ≅ heights: W89 Thm 3.1 proof, (a)⟺(c) (p. 84). | uncited | Sign convention only: Whiteley writes a x + b y + z + c = 0. |
| M9 | `def:pencil-main-picture`, `lem:pencil-x0-main-picture-open`, `rem:pencil-x0-main-component` | ℓ₀ = min dim L(q); main pictures are nonempty and Zariski-open; a vector bundle over them. | W84 Def. 2.4 (p. 273): generic degree of freedom δ(S) = min over pictures, so ℓ₀ = 3 + δ(S_G); "a generic picture is automatically in general position". | uncited | W84's "general position" also asks equality on every sub-incidence structure, and "generic" means transcendental coordinates over ℝ. Here: Zariski-open over any infinite field, for G only. The bundle and main-component language is the project's. |
| M10 | Prose after `def:pencil-x0-attains` and `lem:pencil-config-point-join-rank`: "The panel normals in this definition are the points $p_v$ … Under the polarity it corresponds to the line $p_u \vee p_v$" | Rank of a configuration = rank of the panel-hinge framework with normals p_v = rank of joins. | Polar reading of liftings: W89 §5.1 (p. 87). The triples (x_i, y_i, 1) "also represent lines", and lifting extends them to planes "with the given intersections on a fixed cutting plane z = 0"; coplanarity of a face ⟺ concurrence of the polar planes (Crapo's concurrence geometries). The paraboloid variant is W96 Remark 8.3.2. Rank invariance: CW82 §3.6. | partly cited (rank invariance through `lem:polarity-join`'s chapter) | The polar plane of p_v = (x_v, y_v, z_v, 1) meets z = 0 in the line (x_v, y_v, 1), P_q's body line. So the framework of `def:pencil-x0-attains` has P_q as its section by z = 0. The chapter never says so. |
| M11 | `lem:pencil-config-distinct-realization`, `lem:pencil-selector-plane-contains-nbhd` | A configuration over an admissible picture with z ∈ L(q) is an adjacent-distinct pencil realization. | The scene half is W84 Def. 2.1 (p. 272). The identification of pencil realizations with realizations of S_G (bridge 1) is not in any source read. | uncited | This is the conceptual link the PI asked about. It is stated nowhere in the chapters as "a scene of S_G is a pencil realization". |
| M12 | `lem:pencil-rank-scale-shift` | Adding a globally affine height (a trivial lifting) or scaling preserves the rank. | Projective invariance: CW82 §3.6 (cited in `molecule-modelling.tex`). Trivial liftings: W89 p. 78. | partly cited (by cross-reference) | Minor. |
| M13 | `sec:main-component-flat` intro (lines 842–881), including "Over the reals, $h_v$ gives the velocities normal to the plane $z = 0$ … Crapo and Whiteley \cite{crapoWhiteley1982} describe this correspondence … for the tetrahedron, and note that it holds in great generality (Example~4.4). We prove what we need directly." | The vertical part of a flat motion is a family of affine functions, i.e. face planes of a lifting. | CW82 Ex. 4.4 (pp. 72–73), verified as described: the tetrahedron, "true in great generality, as we shall see in the sequel". The general statement for oriented polyhedra is W82 p. 14 ("the process of lifting a plane picture up to the polyhedral scene in space is an infinitesimal motion of the panel structure"), with the proofs of Thms 3.1 (pp. 18–19) and 3.3 (pp. 20–21). For any incidence structure (covering S_G): W84 §5.1 (pp. 287–288; the vertical velocity of a plate rotating about the line (u, v, w) is ux + vy + w; joints force agreement) and §5.3 (pp. 288–289, crediting W82). | partly cited | An example is cited where the general results exist. W82 is stated for oriented polyhedra, and S_G is not one (the faces at a vertex do not form a cycle), so only W84 §5 covers S_G. "A polyhedron over the picture" should read "a scene": S_G's faces are not a polyhedral surface. CW82's "sequel" is cited as "Whiteley 1982d", which their bibliography lists as "Motions of Trusses and Bipartite Frameworks". "Motions and Stresses of Projected Polyhedra" is their "Whiteley 1981b" (pdf pp. 39–40). So do not cite W82 as the sequel on CW82's authority. |
| M14 | `def:pencil-lifting-planes` (F(q)) | Families h_v of affine functions with h_u − h_v vanishing at q_u and q_v. | F(q) is the face-plane projection of S_G's scene space, = the motions of W84's L(S_G(q)) (Prop. 4.1, M = r, pp. 282–283), = the vertical motions of W84's joined plate structure (§5.1, p. 288) (bridge 3). | uncited | The name "lifting planes" is the project's. |
| M15 | `lem:pencil-lifting-planes-dim` | dim F(q) = dim L(q) at an admissible picture. | Planes determine heights: W84 Prop. 4.1 proof (p. 282, "each vertex … lies on at least one face"). Heights determine planes: W89 Thm 3.1 proof, (a)⟺(c) (p. 84). | uncited | Matches §3 of the note. |
| M16 | `lem:pencil-flat-split` | Motions of the flat hinge framework = 3 (in-plane) + dim F(q) (vertical). | Vertical part: W84 §5.1 (p. 288), joined plate structures; W82 pp. 14, 18–21 for oriented polyhedra. | uncited (the subsection prose, M13, cites CW82) | Neither source treats the in-plane three dimensions: W84 §5.1 keeps only "the significant instantaneous motions … normal to this plane". Sources use joints at the vertices; here, hinges along q_u q_v, which give the same vertical constraints for S_G. |
| M17 | `lem:pencil-lifting-planes-motions` (P_q) | Motions of the plane framework with normals (x_v, y_v, 1) ≅ F(q); rank = 3\|V\| − dim L(q). | W84 Prop. 4.1 and Cor. 4.2(iv) (pp. 282–283): P_q is L(S_G(q)) with star fans (bridge 3). The plane polarity from the joined plate structure: W84 §5.2 (p. 288). P_q is also JJ's rod-and-pin framework (G, −q) (§5, p. 12; bridge 4). | uncited (M20's prose calls P_q "a framework of this kind" for JJ) | W84 has plate-and-bar frameworks (two bars per edge, meeting at the pin); here a panel-hinge framework at d = 2. Same motion space. W84 is linear algebra and holds over any field. |
| M18 | `lem:pencil-lifting-space-deficiency` | dim L(q) ≥ 3 + def₂(G), by a partition count on P_q. | JJ Lemma 4.1 (p. 8) (rank bound for the body-and-pin graph). JJ's def (p. 7) = the chapter's def₂ (checked). W84 p. 273: δ(S(p)) ≥ \|V\|+3\|F\|−\|R\|−3. For S_G this is 3\|V\| − 2\|E\| − 3, the singleton-partition case. | uncited (internal `lem:relative-deficiency-rank-bound` only) | The partition form is standard body-and-pin counting. Its scene form (Whiteley's count) is the singleton case. |
| M19 | `thm:pencil-flat-rank`, `cor:pencil-flat-attains`, `cor:pencil-flat-x0` | rank R(q, 0) = 6\|V\| − 3 − dim L(q); equality cases. | Classical input: flat motions ≅ scenes (M13, M16). | uncited at the nodes (M13's prose cites CW82) | The exact count in the 3D screw space, and the corollaries, are the project's. |
| M20 | `sec:main-component-jj` prose (lines 1113–1155): "The equality is Jackson and Jordán's theorem on pin-collinear body-and-pin frameworks … Jackson and Jordán's argument is specific to the reals …" | JJ: for a simple G with no isolated vertices, pin-lines generic and pins at their meets, the motions have dimension 3 + def₂(G). P_q is such a framework. JJ's genericity is algebraic independence over ℚ, and their proof moves points in small Euclidean neighbourhoods. | JJ Theorem 7.1 (p. 21): r_RP(G) = 3\|V\| − 3 − def(G), with the rod-and-pin framework of §5 (p. 12) and Lemma 5.2 (p. 13). Genericity over ℚ: p. 12. Euclidean moves: Lemma 4.2's proof (p. 9). All verified. Independent case: W89 Thm 5.4 (p. 92), re-derived as JJ Thm 7.4 (p. 22). Why the generic framework count does not transfer to identified (collinear-bar) frameworks: W84 Remark 2 (p. 287). | partly cited | The description is accurate. Gaps: no item number (Theorem 7.1 is the exact match, not Theorem 7.2(b), and the numbering is the report's); the scene reading via W84 Prop. 4.1 is unsaid; W89 Thm 5.4 is unsaid. Combined with W84 Thm 4.9(iv) (p. 287), JJ Thm 7.1 gives the generic degree of freedom δ(S_G) = def₂(G). That conclusion is stated nowhere in the sources (relevant to Q1). |
| M21 | `thm:pencil-jj-equality` | Over every infinite field, dim L(q) = 3 + def₂(G) at a general picture, derived from KT 5.6 at d = 2. | JJ Thm 7.1 over ℝ (as M20). | cited (the subsection cites JJ; no item) | The every-infinite-field proof through KT 5.6 is the project's, and the chapter says so. |
| M22 | `rem:pencil-x0-flatness` | Over a main picture, a planar-rigid W has all its faces in one plane. | W84 Cor. 4.2(i) (p. 283) on S_{G[W]}; W89 Cor. 3.2 proof (p. 85). | uncited | The passage from a generic picture to every main picture is the project's. The remark is used by no proof. |
| M23 | `K_{2,3}` paragraphs after `lem:pencil-x0-two-hubs-obstruction` (lines 4397–4445): "$L(q)$ consists of the globally affine heights … Where they are collinear … $\dim L(q) = 4$" | The degree of freedom jumps at a special-position picture. | W84 pp. 273–274 (Fig. 2C/2D): "by taking special position pictures we can increase the degree of freedom". | uncited | Minor; illustrative. |
| M24 | `lem:pencil-three-points` | A closed neighbourhood with ≤ 3 members imposes nothing. | W89 Def. 3.2 (pp. 82–83), as P6. | uncited | Elementary. |

## Counts

35 rows: 11 for `pencil.tex`, 24 for `main-component.tex`.

| Status | `pencil.tex` | `main-component.tex` | Total |
|---|---|---|---|
| cited | 0 | 1 (M21) | 1 |
| partly cited | 2 (P4, P9) | 7 (M1, M3, M6, M10, M12, M13, M20) | 9 |
| uncited | 7 | 16 | 23 |
| presented as new | 2 (P2, P8) | 0 | 2 |

The only scene-analysis citation in either file is M3 (W96 §8.3, a survey). The only citation
of the flat-motion correspondence is M13 (CW82 Ex. 4.4, one example). W84 (the paper whose
Prop. 4.1 is the lifting space's second description and P_q), W82 and W89 are cited nowhere,
and none of the three is in `blueprint/src/bibliography.bib`.

## Corrections to `notes/PencilScenes.md` §2 and §3

1. **§3, polarity ("the pencil polarity (`sec:pencil-duality`) is this"): refuted as stated.**
   W96 Remark 8.3.2 (pp. 44–45) is the polarity about the paraboloid, in affine coordinates.
   It takes a lifting of a fixed picture on S to a *parallel* scene on S*: the picture points
   become prescribed face normals. The pencil polarity (`lem:polarity-join`) is x ↦ x^⊥ for
   the standard dot product. It acts on every pencil realization, with no picture fixed. What
   is true: S_G = S_G*, and `lem:pencil-self-dual` is the self-duality of S_G-realizations in
   P³ (bridge 1). The classical source for "polarity exchanges hinge-concurrent and
   panel-hinge" is KT p. 650, W99 pp. 29–30 and CW82 §3.6, not W96. The chapters' other use of
   the polarity (M10) matches W89 §5.1 (p. 87), the cutting-plane reading, of which Remark
   8.3.2 is the projectively equivalent plane-at-infinity version (W89 p. 87 says so).
2. **§2 and §3, JJ "Theorem 7.2(b)".** The statement the chapter uses (a simple graph,
   generic pin-lines, pins at their meets, motions 3 + def) is **Theorem 7.1** (p. 21), with
   the rod-and-pin framework of §5 (p. 12). Theorem 7.2(b) is the multigraph body-and-pin
   version. P_q is literally JJ's rod-and-pin framework at p = −q (bridge 4), which §2 misses.
   All of these numbers are the 2006 report's; the bib cites *DCG* 40 (2008), not checked.
3. **§2, W89 "P. 93 … 'the methods used here do not extend'".** The conjecture is on p. 93;
   the quoted sentence is on p. 94.
4. **§2, W82 "§4.4 (pp. 32–33): K₃,₃ … (Bow; Proposition 4.4)".** Proposition 4.4 (Bow's
   crossing-point insertion) is on p. 30, in §4.3. The K₃,₃ item is Example 4.3, in §4.4
   (pp. 32–33), and ends in Pascal's theorem.
5. **§2, W89 "Corollaries 3.2–3.3 … the dimension of the space of scenes".** Corollary 3.3
   (p. 85) gives the dimension only for structures meeting the sharpness count
   (i = v + 3f − 3 − d and i′ ≤ v′ + 3f′ − 4 on every sub-structure with ≥ 2 faces), as an
   affine space with the first face fixed. It is not a general dimension formula; that comes
   from Theorem 3.1's matroid rank (Q1).
6. **§2, CW82 "as we shall see in the sequel".** The sequel is cited as "Whiteley 1982d",
   whose entry in CW82's bibliography is "Motions of Trusses and Bipartite Frameworks". W82's
   title is listed there as "Whiteley 1981b". The note does not assert the identity, but a
   chapter should not cite W82 as "the sequel" on CW82's authority.
7. **§3, flat row (W82 as a source for `lem:pencil-flat-split`).** W82 is stated for oriented
   polyhedra, and S_G is not one; only W84 §5 (any incidence structure) covers S_G. Neither
   source treats the three in-plane dimensions of `lem:pencil-flat-split`. W84 §5.3 (p. 289)
   itself credits W82 (its reference [18]) for "scenes = motions of the joined structure".

Checked and correct in §2 and §3: CW82 Prop. 4.1 (p. 70), Cor. 4.2 (p. 71), Ex. 4.4
(pp. 72–73); W82 p. 14 (quote verbatim), p. 15, Thms 3.1 and 3.3 with their proofs
(pp. 18–21), §3.4 and Cor. 3.5 (p. 23); W84 Defs 2.1–2.4 (pp. 272–273), §4.1 (p. 282), Prop. 4.1
(pp. 282–283), Cor. 4.2 (p. 283), Thm 4.1 (p. 285), Thm 4.9 (p. 287), §5 (pp. 287–289), §7.2
Remark (p. 292); W89 Thm 3.1 (p. 83), §5.1 (p. 87), Thm 5.4 (p. 92); W96 §8.3 (pp. 44–45 of the
preprint), Remark 8.3.2, Thm 5.1.3 (p. 35); JJ Thm 7.4 = W89 Thm 5.4 (p. 22), and no mention
of scenes or liftings in JJ beyond the titles of references [19] and [22]. §3's rows for
`lem:pencil-lifting-planes-dim` and `lem:pencil-lifting-planes-motions` are correct.

## Side findings for whoever writes the citations

- `blueprint/src/bibliography.bib` has `maxwell1864` = "On the calculation of the equilibrium
  and stiffness of frames" (Phil. Mag. 27, 294–299). The lifting and reciprocal-figure paper
  that W84, W96 and the PI's question refer to is a different paper: Maxwell, "On reciprocal
  figures and diagrams of forces", Phil. Mag. (4) 27 (1864) 250–261 (W84 ref. [9]; W96 [Max]).
  Not in `.refs/`; publisher metadata not checked.
- W96's reference [CrW2] gives Crapo–Whiteley, "Plane stresses and projected polyhedra",
  *Structural Topology* 20 (1993) 55–78, the published form of a preprint that W89 cites
  (relevant to Q4; not checked against publisher metadata).
- W84 p. 271 credits "the standard linear equations for polyhedral scenes and line drawings"
  to Duda–Hart 1975 and two Sugihara papers (its refs. [5], [11], [12]); none is in `.refs/`
  (Q4).
- `REFS.md` says the W99 PDF "carries no printed page numbers on page 1". Its text layer shows
  "21" at the foot of pdf page 1, and pdf page n is printed page 20 + n.

## Open, and who decides

- Whether the bridge items 1–4 go into the chapters as stated, and with which citations: the
  PI, at the open (scope (a) or (b) of the note's §6).
- Whether to cite JJ by theorem number: it needs the published *DCG* numbering checked first
  (not in `.refs/`). Until then, write "see Jackson and Jordán" with no item, per the
  citation bar.
- Whether W84 Thm 4.9(iv) + JJ Thm 7.1 (δ(S_G) = def₂(G) generically, over ℝ) is a second
  derivation of the equality: Q1's share.
