# PENCIL-SCENES recon: the ledger for `pencil-d.tex`, and Q2

*Banked as delivered by a read-only recon agent on 2026-11-09. The coordinator's spot-checks, and the
corrections they found, are in `notes/PencilScenes.md` §5; read that first.*

Read-only recon, 2026-11-09, for the queued phase PENCIL-SCENES (`notes/PencilScenes.md` §5). This
share covers (1) the attribution-ledger rows for `blueprint/src/chapter/pencil-d.tex` and (2) the
note's question Q2, with the observations O1 and O4 in passing. The other two chapters and Q1, Q3
and Q4 belong to other shares.

**Method.** I located every passage of `pencil-d.tex` that states or uses the scene material: the
section structure, then grep for `lifting`, `L(q`, `Jackson`, `\cite`, `trivial`, `polar` and
`scene`. I read the nodes named in the brief in full. Each source claim below was checked by me
against the PDF in `.refs/`. The text-layer PDFs were read with pypdf. For the scan
`whiteley-1982-motions-stresses-projected-polyhedra.pdf` I looked at page images of pp. 13–15 and
18–21 only, so a keyword search of that paper was not possible. Page numbers are the printed ones,
with the offsets in `REFS.md` *Catalogue of `.refs/`*; I checked each offset against a printed
header. Whiteley 1996 is the author's preprint, and its page numbers are the preprint's. Line
numbers are those of `pencil-d.tex` at `499564a7`.

**Notation.** S_G is the incidence structure of `notes/PencilScenes.md` §3: its points are the
bodies, its faces are the closed neighbourhoods N[v] (one face per body), and w lies on face v iff
w ∈ N[v]. In the tables, #V is the number of bodies.

## 1. Source anchors used (all checked in the PDFs)

| Source | Item, printed page | What it says |
|---|---|---|
| Whiteley 1984, *Discrete Appl. Math.* 9, 269–295 (`.refs/whiteley-1984-scene-analysis-motions-frameworks.pdf`) | §2.1, pp. 271–272 | Incidence structure S = (V, F, R). No face plane is vertical "for convenience (and following convention)" (p. 271). Each face plane is a_k x + b_k y + z + c_k = 0, and each incidence gives one linear equation (1) in the heights and the plane coefficients (p. 272). "Every picture with at least one face has a 3-dimensional set of trivial scenes" (p. 272). |
| | Def. 2.1–2.2, p. 272; Def. 2.3–2.4, p. 273 | Scenes S(q, r) realizing a picture; flat, folded and sharp ("each face lies in a different plane"); degree of freedom δ = dim(scenes) − 3; general position; generic means algebraically independent transcendentals; δ(S(p)) ≥ δ(S) ≥ \|V\| + 3\|F\| − \|R\| − 3 (p. 273). |
| | §4.1, Prop. 4.1, pp. 282–283; Cor. 4.2, p. 283 | Row reduction gives the reduced plate framework L(S(p)), with a fan of bars along the line (x_w, y_w, 1) at each vertex w. Scenes ≅ instantaneous motions with M = r. Flat/rigid, foldable/shaky, sharp/completely shaky, and equal degrees of freedom. |
| | §5.1–5.3, pp. 287–289 | Joined plate structure: plates in a plane, joints at points, vertical velocities u x + v y + w. At a joint (x, y, 1), (u₁ − u₂, v₁ − v₂, w₁ − w₂)·(x, y, 1) = 0. A polarity of the plane gives the plate-and-bar framework (§5.2, p. 288), and adding the joint heights gives the scene matrix A (§5.3, pp. 288–289). P. 288: "It has long been known that ordinary projective transformations do not change the static and instantaneous kinematic properties of structures." |
| | §7.2, Def. 7.2 and Remark, p. 292 | A picture in K-space has points in K-space. A scene in (K+1)-space gives each face a **non-vertical hyperplane** a₁x₁ + … + a_K x_K + x_{K+1} + a_{K+1} = 0, and a scene is flat when all faces get one hyperplane. Remark: plane pictures of 4-dimensional scenes (hyperplane faces) give **non-linear** equations (the term c z). |
| | §7.3, p. 293 | For a K-space picture the reduced matrix has K + 1 columns per face. It is a (generalized) bar-and-body framework only when K + 1 = n(n+1)/2: "the reduction map is undefined for K = 3, K = 4, K = 6, etc." |
| Whiteley 1989, *Discrete Comput. Geom.* 4, 75–95 (`.refs/whiteley-1989-matroid-on-hypergraphs.pdf`) | §2.1, p. 78 | A scene over a picture is a choice of heights z with each face's points in a plane, given by a 4×4 determinant; "for a fixed picture this gives one linear constraint on the unknowns z_j". |
| | Def. 3.1, p. 82; Thm 3.1, p. 83 (proof p. 84); Cor. 3.2, p. 84; Cor. 3.3, p. 85 | General scenes, with the incidence linear in r₁, r₂, r₃, q₃. In the proof of (a)⟺(c), heights over a general picture determine the face planes (p. 84). The count, sharpness, and the dimension of the space of scenes. All over ℝ, generic over ℚ. |
| | §4, Def. 4.1–4.4, Thms 4.1–4.2, pp. 85–87 | The k-plane matroid. "For k > 3, we have interpretations in terms of pictures in (k−1)-space and scenes in k-space [17, Section 7]" (p. 86), with hyperplane faces. Generic results only. |
| Whiteley 1996, preprint of *Contemp. Math.* 197 (`.refs/whiteley-1996-matroids-discrete-geometry.pdf`, bib `whiteley1996`) | §8.3, pp. 44–45 | A lifting of a (d−1)-picture is a d-scene with hyperplane faces, A_j x_i + … + C_j z_i + w_i + D_j = 0. Picture Theorem 8.3.1 [Wh8 = Whiteley 1989]. Remark 8.3.2: a polarity takes S to S\*, and the affine setting excludes vertical planes and points at infinity. Cites [CrW4] and [CRy] for related liftings. |
| Crapo–Whiteley 1982, *Structural Topology* 6, 43–82 (`.refs/crapo-whiteley-1982-statics-of-frameworks.pdf`, bib `crapoWhiteley1982`) | §3.6, p. 68 | "Any non-singular collineation … will transform an instantaneous motion into an instantaneous motion … the instantaneous motions and infinitesimal rigidity of a panel structure are projectively invariant" (3-space). Correlations too, in 3-space. |
| | §5, p. 75 | Articulated panel structures in n-space, joined along (n−1)-extensors: "Projective invariance of these motions still holds in any dimension, but duality causes serious difficulties". Asserted without proof. |
| Whiteley 1982, *Structural Topology* 7, 13–38 (`.refs/whiteley-1982-motions-stresses-projected-polyhedra.pdf`, scan, no bib entry) | p. 14; p. 15; Thm 3.1 with proof, pp. 18–19; Thm 3.3 with proof, pp. 20–21 | "The process of lifting a plane picture up to the polyhedral scene in space is an infinitesimal motion of the panel structure, composed of panels on the faces and hinges along the edges of the flat projection" (p. 14). Each face panel rotates about the line where its face plane meets the projection plane (p. 19), and the converse holds (pp. 20–21). Stated for **oriented polyhedra** (each hinge an edge between two faces). |
| White–Whiteley 1987, *SIAM J. Alg. Disc. Meth.* 8 (`.refs/white-whiteley-1987-algebraic-geometry-of-motions.pdf`, bib `whiteWhiteley1987`) | p. 2; §5, pp. 29–31 | "The k-frames first appeared in scene analysis — the study of hyperplane scenes in R^k projected into pictures in R^{k−1}" (p. 2). §5 restates Whiteley 1984's correspondence for 3-frames. |
| Jackson–Jordán, EGRES TR-2006-06 (`.refs/jackson-jordan-2006-pin-collinear-tr.pdf`, bib `jacksonJordan2008pin`, report pages) | p. 3; Thm 7.2, p. 21; Thm 7.4, p. 22 | Pin-collinear: "the pins incident to each body lie on a common line" (p. 3). Thm 7.2(b): a body-and-pin framework in ℝ² with collinear pins at each body and rank 3\|V\| − 3 − def(G). Thm 7.4 = Whiteley 1989 Thm 5.4. |
| Katoh–Tanigawa 2011, *Discrete Comput. Geom.* 45 (bib `katohTanigawa2011`) | Thm 5.6, p. 670 | A panel-hinge realization in ℝ^d of rank D(\|V\| − 1) − def(G̃). Its proof cites "[4, Sect. 3.6]" (Crapo–Whiteley 1982) for projective invariance (p. 670). |

## 2. The ledger for `pencil-d.tex`

Status: **cited** (a `\cite` at the passage covers the classical claim); **partly cited** (named by
attribution, or reached through a `\cref` whose target cites, but the main classical source is
missing); **uncited** (classical content with no attribution, not framed as new); **presented as
new** (framed as the chapter's own construction or device where a source has it). The column
*Classical source* says "none found" when no source in `.refs/` has the claim.

| # | Label or passage (line) | Claim, in one line | Classical source (checked) | Status now | Discrepancy |
|---|---|---|---|---|---|
| 1 | `sec:pencil-d` intro, ¶1 (4–20) | Pencils in dimension d. At d = 2 a pencil realization is Jackson–Jordán's pin-collinear body-and-pin framework; the theorem strengthens KT Thm 5.6. | JJ TR p. 3 (definition), Thm 7.2(b) p. 21; KT 2011 Thm 5.6 p. 670 | cited (`jacksonJordan2008pin`, `katohTanigawa2011`) | JJ and KT work over ℝ (affine ℝ², ℝ^d); the chapter works over infinite fields and projectively (pins at infinity allowed). No scene material here. |
| 2 | `sec:pencil-d` intro, ¶2 (22–55) | Road map: configurations, the flat rank, Jackson and Jordán's equality, the lift of nondegenerate realizations. | The carrier is classical: Whiteley 1984 §2 and §4–5; Whiteley 1996 §8.3; the lift is Whiteley 1984 §7.2 at K = 3 (see Q2) | uncited (no lineage given; it defers to `sec:pencil-roadmap`) | — |
| 3 | `sec:pencil-d` intro, ¶3 (57–68), with `lem:pencil-d-point-configuration` (184) | Polar form: with independent adjacent normals, a pencil realization is a point configuration whose closed neighbourhoods each lie in a plane Π_v. | S_G as an incidence structure: Whiteley 1984 Def. 2.1, p. 272. The polar of a panel structure: Crapo–Whiteley 1982 §3.6, p. 68 (3-space). For planes through closed neighbourhoods in P^d, d ≥ 4: none found | uncited | Crapo–Whiteley p. 75: in n-space "duality causes serious difficulties". The chapter's polar form for d ≥ 4 is a description of the data (normals as points), not a rank-preserving correlation, and the chapter does not claim more. The S_G reading of "closed neighbourhoods in planes" is unsaid. |
| 4 | `sec:pencil-d-carrier` intro (333–338) | "A configuration in dimension d lifts a planar picture by d − 2 heights, each of them in the lifting space L(q)". | One height: Whiteley 1984 Def. 2.1–2.2, p. 272; Whiteley 1996 §8.3, p. 44 ("lifting"). d − 2 heights: none found; the contrast is Whiteley 1984 §7.2 Remark, p. 292 | uncited (the scene reading is reached only through `\cref{def:pencil-lifting-space}`, whose passage cites Whiteley 1996 §8.3 at `main-component.tex`:177) | Whiteley's faces are hyperplanes; the chapter's faces are 2-planes (codimension d − 2). |
| 5 | `def:pencil-d-configuration` (340), with the paragraph after it (361–366) | b_v = (x_v, y_v, z¹_v, …, z^{d−2}_v, 1); its rank is that of the panel-hinge framework with normals b. If every z^i ∈ L(q), each closed neighbourhood lies in a plane. | d = 3 points over a picture: Whiteley 1984 Def. 2.1, p. 272. d − 2 heights over one picture: none found. Reading the rank at the panel-hinge framework with these normals: none found (the project's) | uncited | Whiteley's scene carries the face planes r as data; the chapter keeps only heights, and the planes are recovered at admissible pictures (`lem:pencil-lifting-planes-dim`). ℝ and transcendental generics there; any field here. |
| 6 | `def:pencil-d-affine-heights-map` (368) | σ(ξ, η, ω) = (ξ, η, a^iξ + c^iη + e^iω, …, ω): a face is the graph of d − 2 affine functions of the picture. | d = 3, a non-vertical face plane a x + b y + z + c = 0: Whiteley 1984 §2.1, pp. 271–272. d ≥ 4: none found; compare Def. 7.2 (hyperplane faces) and the §7.2 Remark, p. 292 | uncited | σ's image is a projective plane of P^d that projects isomorphically onto the picture plane. Because each face is a graph over the picture plane, the incidence equations stay linear. With hyperplane faces over a plane picture, the Remark notes that they become quadratic. |
| 7 | `lem:pencil-d-config-realization` (388) | Over an admissible picture with z ∈ L(q)^{d−2}, the configuration is a pencil realization with independent adjacent normals. | The scene part (each face's points lie on its plane): Whiteley 1984 Def. 2.1, p. 272. The pencil part: none found (the project's) | uncited | — |
| 8 | `lem:pencil-d-condition-linear` (1239), with the prose before it (1232–1237) | A closed neighbourhood spans dimension ≤ 3 iff each z^i is affine on it; then Π_v = im σ_v and Π_v^⊥ is spanned by the n^i. All neighbourhoods together iff z ∈ L(q)^{d−2}. | d = 3: Whiteley 1989 §2.1, p. 78 ("for a fixed picture this gives one linear constraint on the unknowns z_j") and Def. 3.1, p. 82; Whiteley 1984 eq. (1), p. 272. d ≥ 4: none found | uncited (the proof says only "at d = 3 this is `lem:pencil-condition-linear`") | Whiteley **assumes** non-vertical faces (Whiteley 1984 p. 271; 1989 p. 82). The chapter **derives** non-verticality from admissibility (three non-collinear picture points). |
| 9 | `def:pencil-d-x0-attains` (423), `lem:pencil-d-x0-attains-three` (437), `lem:pencil-d-x0-one-witness` (508) | The general configuration attains: generic rank over L(q)^{d−2}. One witness over a main picture suffices. | none found. The analogue of the "main picture" (least dim L(q)) is Whiteley's general position, δ(S(p)) = δ(S), Def. 2.4, p. 273 | uncited (nothing owed beyond the L(q) pointer) | Whiteley's general position also asks the equality on every sub-incidence structure; a main picture asks only the least dim L(q). |
| 10 | `lem:pencil-d-rank-collineation` (452) | An invertible linear map g applied to the panel normals preserves the rank. | Crapo–Whiteley 1982 §3.6, p. 68 (3-space) and §5, p. 75 (any dimension, asserted); Whiteley 1984 §5.2, p. 288 ("long been known"); KT 2011 p. 670 cites Crapo–Whiteley §3.6 | uncited | Crapo–Whiteley transform the points and hinges by a collineation; the lemma transforms the normals by g, which moves the panels by the inverse transpose. The n-space case is asserted on p. 75 without proof, over ℝ. The proof here works over any field. |
| 11 | `lem:pencil-d-rank-scale-shift` (485) | (q, z) and (q, Tz + a) have equal rank, for T invertible and a ∈ Aff(q)^{d−2}. | The shift a: adding a trivial scene, Whiteley 1984 p. 272 (trivial scenes) and Def. 2.3, p. 273 (flat), with projective invariance (row 10). The mixing T of several heights: none found | uncited | Only the T part needs several heights. It settles O1 (§4). |
| 12 | `sec:pencil-d-induction` intro and notation list (1153–1230) | "The planar objects … the lifting space L(q) and its lifting system … So does Jackson and Jordán's equality, which concerns L(q) alone". The pencil configuration space over an admissible q is L(q)^{d−2}. | JJ TR Thm 7.2(b), p. 21. Scene reading: Whiteley 1984 §2 and §4; the generic dimension is Q1 (Whiteley 1989 Thm 3.1, p. 83) | partly cited (JJ named, with `\cref{thm:pencil-jj-equality}`; the `\cite` is at `main-component.tex`:105 and :1123; no scene lineage) | JJ prove an existence statement over ℝ for pin-collinear frameworks. The "equality" dim L(q) = 3 + def₂(G), at a general picture over an infinite field, is the project's reformulation, derived from KT Thm 5.6 at d = 2 (`main-component.tex`:105). |
| 13 | `sec:pencil-d-flat` intro (1315–1332) | The flat configuration is the planar one embedded; its rank is read off P_q; with JJ's equality, dim L(q) = 3 + def₂(G). | P_q's motions = scenes: Whiteley 1984 Prop. 4.1 and Cor. 4.2(iv), pp. 282–283. Origin: Whiteley 1982 pp. 14, 18–21. JJ TR Thm 7.2(b), p. 21 | partly cited (JJ by name and `\cref`; no Whiteley) | As row 12. |
| 14 | `thm:pencil-d-flat-rank` (1336) | The rank of (q, 0) is D(#V − 1) + 3 − dim L(q). Its proof: rank(P_q) = 3·#V − dim L(q), plus the embedding; second paragraph: the ⋀²Ĥ part of a motion is a family of lifting planes, and the complement part is constant. | The d = 2 count: Whiteley 1984 Prop. 4.1 and Cor. 4.2(iv), pp. 282–283. P_q is Whiteley's reduced plate framework of S_G(q), with the fan at each vertex taken as the star from its own plate, so that the two collinear-fan bars of an edge meet in one pin. The lifting-plane motions: Whiteley 1984 §5.1–5.3, pp. 287–289. Origin: Whiteley 1982 Thms 3.1 and 3.3, pp. 18–21. The constant D − 3 part: none found (the project's embedding) | uncited (the classical part is reached only through `\cref{lem:pencil-lifting-planes-motions}`) | Whiteley 1982 covers **oriented polyhedra** only, and S_G is not one in general. The statement for a general incidence structure is Whiteley 1984 §5 (joined plate structures). Whiteley's framework is plate-and-bar, P_q is body-and-pin, and the two are line-equivalent (Whiteley 1984 Def. 3.4). Both are over ℝ. |
| 15 | `cor:pencil-d-flat-attains` (1392), `cor:pencil-d-jj-flat` (1444), `rem:pencil-d-flat-class` (1472) | Flat attainment when dim L(q) ≤ 3 + def_d. By JJ's equality, the graphs with def₂ = def_d attain. | JJ TR Thm 7.2(b), p. 21. The bound dim L(q) ≥ 3 + def₂: its singleton-partition case is Whiteley 1984's count ρ(S), p. 273, on S_G: #F = #V, #R = #V + 2#E for simple G, so dim L(q) ≥ 3·#V − 2#E. The partition form is Q1's | partly cited (JJ named, `\cref`) | As row 12. Whiteley's count is for the whole structure; the project's def₂ maximizes over partitions. |
| 16 | JJ uses in the induction: `thm:pencil-d-contract-additive` (1850; prose 1891–1900), `lem:pencil-d-glued-ends` (3112; 3140–3150 count, 3162 JJ) | Apply JJ's equality at H, G/H and the merged graph G′; "lifting planes constant on the parts", dimension ≥ 3·#P − 2d_G(P). | JJ TR Thm 7.2(b), p. 21. The count: as row 15 | partly cited (JJ named, `\cref`) | As row 12. |
| 17 | `sec:pencil-d-lift` intro (5004–5022) | "Instead we keep the parametrization in dimension three and lift": d − 3 functions on the bodies, each a linear form of the points on every closed neighbourhood. | A single lift is a scene in 4-space over the 3-space picture b⁰: Whiteley 1984 Def. 7.2, p. 292 (K = 3); Whiteley 1996 §8.3, p. 44 (d = 4); generic theory in Whiteley 1989 §4, pp. 85–87 (k = 4). See Q2 | presented as new | The chapter uses projective coordinates where Whiteley uses affine ones. The base picture is in special position (each face's points coplanar). Several lifts at once give codimension-m faces, which no source treats. |
| 18 | `def:pencil-d-lift` (5168), with the paragraph after it (5208–5214) | The lift space 𝓛(b⁰, Π⁰) of pairs (ζ, φ) with ζ_w = φ_v(b⁰_w); trivial lifts; L(b⁰); the lifted normals and the 2-planes Π_v. | 𝓛 is the space of Whiteley 4-scenes over b⁰ (Def. 7.2, p. 292) modulo, at each face, the forms that vanish on Π⁰_v. A **trivial lift = a flat scene** ("flat if all faces are assigned the same hyperplane", p. 292; Def. 2.3, p. 273) | presented as new ("lift", "trivial" are defined with no reference to scenes) | Whiteley's face is a hyperplane of the 4-space; the chapter's Π_v is the projective plane cut from it by the prism over Π⁰_v (Q2). |
| 19 | `lem:pencil-d-lift-realization` (5218) | (1) Lifts are nondegenerate pencil realizations. (2) L(b⁰) is the set of ζ with, at every body, one linear form ψ_v on K⁴ agreeing with ζ on N[v]. (3) Rescaling points and GL₄ act on the lift spaces and keep ranks. | (2) is exactly the height part of Whiteley 1984 Def. 7.2 at K = 3 (with r_v = −ψ_v). (3), the collineation half: Crapo–Whiteley §3.6, p. 68, via row 10 | uncited | Projective in place of affine (no point at infinity or vertical face excluded). |
| 20 | `lem:pencil-d-lift-one-witness` (5317) | Defines L̃(b⁰) = {(ζ, ψ) : ζ_w = ψ_v(b⁰_w)} as the kernel of A(b⁰). One lift at a realization of least dim L̃ suffices. | L̃(b⁰) **is** Whiteley's space of 4-scenes over b⁰ (Def. 7.2, p. 292), and A(b⁰) is its scene matrix (Whiteley 1984 §7.3 "matrix A", p. 293; Whiteley 1996 §8.3 lifting matrix M(S, r), p. 45). "Least dim L̃" is the analogue of general position (Def. 2.4, p. 273). The semicontinuity argument: none found (the project's) | uncited | As row 19. |
| 21 | `lem:pencil-d-lift-no-rigid` (5914) | At a configuration base (q, z¹): L(b⁰) = L(q), so a lift by ζ ∈ L(q)^m is the configuration (q, (z¹, ζ)); dim L̃(b′) = dim L(q′) + #V; some attaining z has pairwise distinct planes h_v. | "Pairwise distinct planes" is a **sharp** scene (Whiteley 1984 Def. 2.3, p. 273). The identification L(b⁰) = L(q) at a 3-scene base: none found | uncited | The extra #V is one free hyperplane per face through each face's plane, the pencil of 4-space hyperplanes containing it (Q2). |
| 22 | `sec:pencil-d-generic` intro (5499–5520) | "We lift a nondegenerate configuration by attaining heights"; "the rest of W₀ lifts only trivially". | As rows 17–18 (trivial = flat) | uncited | — |
| 23 | Prose before `lem:pencil-d-ear-free` (6237–6250), and `lem:pencil-d-ear-free` (6357) | At a general picture of Y, dim L_Y(q) = 3 + def₂(Y) = 4 by JJ, so every lift of Y is trivial; planes h_v pairwise distinct. | JJ TR Thm 7.2(b), p. 21. In Whiteley's terms, δ(S_Y(q)) = dim L_Y(q) − 3 = 1 (Def. 2.4, p. 273), so the scenes over q are spanned by the flat ones and the one given by z, and the lifts are flat. Sharp: Def. 2.3, p. 273 | partly cited (JJ named, `\cref`) | As row 12. |

**Counts (23 rows): 1 cited, 5 partly cited, 15 uncited, 2 presented as new.**

- Cited: row 1.
- Partly cited: rows 12, 13, 15, 16 and 23.
- Uncited: rows 2–11, 14 and 19–22. Row 9 owes nothing, so 14 uncited rows owe a citation.
- Presented as new: rows 17 and 18.

**Not rowed (out of scope; their prose does not invoke scene material):** the steps of the
induction from `sec:pencil-d-cut` to `sec:pencil-d-coverage`. They take heights in L(q)^{d−2}
and restrict them (`lem:pencil-d-lifting-restrict`, which is the restriction of a scene to a
sub-incidence structure and is elementary). Also out of scope: `sec:pencil-d-stable`, the
reduction and nondegeneracy sections, and `lem:pencil-d-steer`, a parametrization of point–plane
realizations of S_G in P³.

**The most important uncited items.**

1. Row 14 (`thm:pencil-d-flat-rank`) and row 8 (`lem:pencil-d-condition-linear`): the classical
   content of the flat rank (Whiteley 1984 Prop. 4.1 and §5) and of "coplanarity is linear in the
   heights" (Whiteley 1989 p. 78). The chapter states both with no source.
2. Rows 17–20 (Part C): the chapter's lift space L̃(b⁰) is literally Whiteley's space of scenes in
   4-space over a 3-space picture (1984 Def. 7.2; 1996 §8.3), and "trivial lift" is his "flat
   scene". The chapter presents both as its own device.
3. Row 10 (`lem:pencil-d-rank-collineation`): projective invariance is Crapo–Whiteley 1982 §3.6
   (p. 68), and p. 75 asserts it in every dimension. KT already cite §3.6 for it, and the bib key
   exists.
4. Rows 12, 13, 15, 16 and 23: JJ's equality is named six times (lines 1169, 1317, 1326, 1457, 1893
   and 3162) and reached by `\cref` alone twice more (6247, 6418), with no `\cite` in this
   chapter, and its reading as the generic dimension of the scene space of S_G (Q1) is unsaid.

## 3. Q2: is Part C's lift a space of scenes?

**Verdict.** Yes, one lift at a time. A single lift (m = 1) is a scene in Whiteley's §7.2 sense
with K = 3 for the incidence structure S_G. The 3-space picture is the base points b⁰ and the
faces are **hyperplanes** of the 4-space. The chapter's pair space L̃(b⁰) is that scene space
exactly, and its 𝓛(b⁰, Π⁰) is the quotient that keeps only each face hyperplane's trace over the
base plane Π⁰_v. So §7.2 does cover each lift. Two things are outside every source in `.refs/`:
the base whose picture is in special position, with its faces given as planes in advance, and
d − 3 lifts taken together, which have faces of codimension d − 3. The second is a direct product
of single lifts, so it adds no new mathematics.

**Precisely.**

- **Incidence structure.** S_G, the same as at d = 3: one face per body, w on face v iff
  w ∈ N[v].
- **Picture.** The base points b⁰_w ∈ K⁴. In the affine chart b⁰_{w,4} = 1 they are a 3-space
  picture (Whiteley 1984 Def. 7.2 with K = 3; Whiteley 1996 §8.3, a "(d−1)-picture" with d = 4).
  The picture is in special position: the points of each face lie on the plane Π⁰_v of P³. So
  the base (b⁰, Π⁰) is itself a point–plane realization of S_G in P³, and Whiteley's picture
  carries no such face data.
- **Face dimension for one lift.** Whiteley's scene gives face v the non-vertical hyperplane
  ζ = ψ_v(x, y, z, 1) of the 4-space, r_v = −ψ_v in his sign convention. The scene space is
  {(ζ, ψ)}, which is the chapter's L̃(b⁰) (`lem:pencil-d-lift-one-witness`), and its height
  projection is L(b⁰) (`lem:pencil-d-lift-realization` (2)). The chapter's 𝓛(b⁰, Π⁰) keeps
  φ_v = ψ_v restricted to Π⁰_v. The map L̃ → 𝓛, (ζ, ψ) ↦ (ζ, ψ restricted to Π⁰), is onto (a
  form on Π⁰_v extends to K⁴), and its kernel is the span over v of the forms K·n_v vanishing on
  Π⁰_v, of dimension #V. So dim 𝓛 = dim L̃ − #V, the extra #V that
  `lem:pencil-d-lift-no-rigid` computes. The lifted face Π_v of `def:pencil-d-lift` is a
  **projective plane of P⁴**: the intersection of Whiteley's hyperplane with the vertical prism
  over Π⁰_v. Trivial lifts are flat scenes.
- **Face dimension for m = d − 3 lifts.** The m lifts are m independent 4-scenes over one
  3-space picture. Taken together, each face is the graph of an affine map from 3-space to K^m, a
  3-flat of codimension m in d-space (in the chapter's reduced form, the projective plane Π_v of
  P^d). The equations are linear because each face is a graph over the picture space, the same
  reason that keeps the d − 2 heights linear.
- **At configuration bases.** Suppose the base's points are finite (b⁰_{w,4} ≠ 0), its faces are
  non-vertical (n_v has a nonzero third coordinate), and each face has three points with
  independent picture points. Then the base is a classical scene in 3-space over the plane
  picture q′ (Whiteley 1984 Def. 2.1), L(b⁰) = L(q′), and the lift is the configuration
  (q′, (z′, ζ¹, …, ζ^m)): **d − 2 independent scenes over one plane picture**. This is shown in
  the proof of `lem:pencil-d-lift-no-rigid` ("Its lifts", "The least lift space"). There the
  chapter imposes these open conditions at a general nondegenerate realization of the graphs it
  treats. I did not check whether the third condition holds at every nondegenerate realization of
  a hub. On that open set of bases, Part C is the construction of `def:pencil-d-configuration`.
  What is new in Part C is the distribution of the base: a general nondegenerate realization,
  parametrized by `lem:pencil-d-steer`, in place of a general picture with general heights in
  L(q).
- **No framework reading of a single lift in Whiteley's correspondence.** Whiteley 1984 §7.3
  (p. 293): for K = 3 the reduced matrix has 4 columns per face, which is not n(n+1)/2, and "the
  reduction map is undefined for K = 3". The chapter reads the rank at the panel-hinge framework
  with the lifted normals, which is a different object from Whiteley's reduced matrix.

**Does any source in `.refs/` treat it?** For the single lift as a scene over an arbitrary
3-space picture: Whiteley 1984 §7.2 (Def. 7.2, p. 292) and Whiteley 1996 §8.3 (pp. 44–45). Whiteley
1989 §4 (pp. 85–87, k = 4) gives generic counts only, and White–Whiteley 1987 (p. 2) names
"hyperplane scenes in R^k projected into pictures in R^{k−1}". The generic results do not apply at
Part C's bases, whose faces are coplanar in the 3-picture. No source treats a 3-picture with given
face planes, faces of codimension > 1, or the projective form. Whiteley 1996 §8.3 cites two
sources outside `.refs/` that may come closer: Crapo–Whiteley [CrW4], "3-stresses in 3-space and
projections of 4-polytopes: reciprocals, liftings and parallel configurations" (York University
preprint, 1994), which is liftings from 3-space to 4-space; and Crapo–Ryan [CRy], "Spatial
realizations of linear scenes", *Structural Topology* 13. These are leads for Q4.

**d − 2 independent heights over one plane picture** (a configuration in P^d whose closed
neighbourhoods each span a projective plane). **No source in `.refs/` names it.** I searched the
text layers of all 40 PDFs in `.refs/` for `scene`, `lifting(s)` and `heights` (the Whiteley 1982
scan has no text layer); the hits outside the
Whiteley papers are only titles in reference lists. I read Whiteley 1984 §7, Whiteley 1989 §4–5,
Whiteley 1996 §8.3, White–Whiteley 1987 §5 and Crapo–Whiteley 1982 §5. The 1982 scan could not be
searched. The nearest passage is Whiteley 1984 §7.2's Remark (p. 292): plane pictures of
4-dimensional scenes with **hyperplane** faces give non-linear equations. Faces that are 2-planes
over the picture plane are the linear alternative, and their scene space is the (d − 2)-fold
product of the classical one, L(q)^{d−2} on the heights. So a chapter can present the
construction as "d − 2 scenes over one picture", with the Remark as the contrast. Doing so claims
nothing deep as new.

## 4. O1 and O4

- **O1 holds, over every field, and the chapter does not state it.** `lem:pencil-d-rank-scale-shift`
  (Lean `Graph.finrank_span_rigidityRows_ofNormals_heights_linearEquiv_add_affineLifts`, with
  `[Field K]`, any picture q, any heights z, T a linear equivalence of `Fin m → K`, and each
  a_i ∈ `G.affineLifts q`) gives rank(q, z) = rank(q, Tz + a). Let z and z′ be two (d−2)-tuples
  whose classes modulo Aff(q) span the same W. The maps A, B: K^{d−2} → W, e_i ↦ [z^i] and
  e_i ↦ [z′^i], are onto with kernels of equal dimension. So B = A∘S for an invertible S (match
  complements of the kernels through W, and the kernels by any isomorphism). Then z′ = Tz + a with
  T = Sᵀ and a ∈ Aff(q)^{d−2}, and the lemma applies. The lemma does not need z ∈ L(q), so O1 also
  holds with W taken in K^V/Aff(q).
- **O4 holds, with one refinement.** The hinge C(b_u, b_v) = *(b_u ∨ b_v)
  (`def:panel-support-extensor`, with * linear), and the coordinates of b_u ∨ b_v are the 2×2
  minors of the two points (`pencil-d.tex`:577). For two different heights i ≠ j, the minor
  z^i_u z^j_v − z^j_u z^i_v is bilinear, and it occurs exactly when d − 2 ≥ 2. At d = 3 every
  minor is affine in the one height. So the hinges are affine in the heights only at d = 3. The
  refinement: in every dimension they are affine in **each** height separately. In Part C at
  d = 4 (one lift) the hinges are affine in the lift parameter ζ, because the base's own height is
  fixed there.

## 5. Corrections to `notes/PencilScenes.md`

1. **§5 Q2 and the §3 row for `def:pencil-d-lift`.** "Whiteley 1984 §7 treats K-space pictures
   with hyperplane faces only" is accurate, but a single lift **is** such a hyperplane-face scene
   (K = 3), so §7.2 covers it. What §7 lacks is several lifts at once, the reduction of each face
   to its 2-plane trace, the projective form, and a base with given face planes.
2. **§3 row on the flat motions.** Whiteley 1982 is stated for oriented polyhedra (each hinge an
   edge between two faces). S_G is not one in general, so for S_G the general-incidence statement
   is Whiteley 1984 §5.1–5.3. Cite Whiteley 1982 as the origin only.
3. **Omissions from §2 and §3, not errors.**
   - Crapo–Whiteley 1982 §3.6 (p. 68) and §5 (p. 75), projective invariance, are the source for
     `lem:pencil-d-rank-collineation`.
   - Whiteley 1989 p. 78 is the source of "coplanarity is linear in the heights"
     (`lem:pencil-condition-linear`, `lem:pencil-d-condition-linear`).
   - Whiteley's flat and sharp scenes (Def. 2.3, p. 273) are the chapter's trivial lifts and
     "planes h_v pairwise distinct".
   - None of `lem:pencil-d-rank-collineation`, `lem:pencil-d-rank-scale-shift` or
     `lem:pencil-d-condition-linear` has a §3 row.
4. **Checked and correct:** the §2 entries for Whiteley 1984 (Defs 2.1–2.4, §4.1, Prop. 4.1,
   Cor. 4.2, §5, §7.2 Remark, Thm 4.9 on p. 287), Whiteley 1989 (Thm 3.1 p. 83, Cors 3.2–3.3
   pp. 84–85), Whiteley 1996 §8.3 and Remark 8.3.2, Whiteley 1982 (pp. 14, 18–21), and JJ (Thm
   7.2(b), Thm 7.4 = Whiteley 1989 Thm 5.4). I did not check Whiteley 1984 Thm 4.1 (p. 285),
   Whiteley 1989 Thm 5.4 or p. 93, or Whiteley 1996 Thm 5.1.3.

## 6. Open, and who decides

- **The PI, at the open (scope (a)–(c)):** whether Part C's exposition says "a lift is a scene
  over the 3-space picture b⁰ (Whiteley 1984 Def. 7.2, K = 3), reduced to the base planes". Also
  whether `def:pencil-d-configuration` is introduced as "d − 2 scenes over one picture", with the
  §7.2 Remark as the contrast.
- **The bibliography:** Whiteley 1982, 1984 and 1989 have no bib entries. `crapoWhiteley1982`,
  `whiteley1996`, `whiteWhiteley1987`, `jacksonJordan2008pin` and `katohTanigawa2011` exist.
- **The Q1 share:** whether def₂(G) = δ(S_G) at a generic picture, the reading behind rows 12–16
  and 23.
- **The Q4 share:** [CrW4] and [CRy], cited in Whiteley 1996 §8.3 and not in `.refs/`, which are
  the likeliest sources for Part C's lift.
- **Unchecked:** whether every nondegenerate realization meets the third open condition of Q2's
  configuration-base reduction at hubs.
