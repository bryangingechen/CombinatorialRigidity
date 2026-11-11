# PENCIL-SCENES recon: the provenance of Q1's merging lemma

Read-only literature recon, 2026-11-11, for `notes/PencilScenes.md` §5 *Open leads* (the merging
lemma's provenance). Read `notes/pencil-scenes/q1-count.md` §3.3 first: it states and proves the lemma.
Sources were read in the PDFs in `.refs/` (pypdf text; for the scanned Whiteley 1989 pages quoted
below, the page images too). Page numbers are the printed ones; "pdf p." marks the others. A claim
marked *(inferred)* is this agent's derivation, not something on the page.

## 0. What was looked for

Write g(X) = |A(X)| + 3|B(X)| − 3 for a set X of incidences of S_G (A: the points it touches, B: the
faces). The lemma has three parts; each verdict below says which part, if any, a source contains.

- **(M1) The union defect.** For disjoint X, Y: g(X ∪ Y) = g(X) + g(Y) + 3 − |A(X) ∩ A(Y)| −
  3|B(X) ∩ B(Y)|. So merging two parts of a partition does not raise Σ g when they share a face or
  three points.
- **(M2) The face merge.** Merging parts that share a face makes an optimal partition face-grouped.
  This half works for every incidence structure (V, F; I), not just S_G. *(Inferred)* It gives r_g(I)
  = v + 3f − 3 − max over partitions 𝓕 of F of [3(|𝓕| − 1) − Σ_points (w_𝓕(p) − 1)], where w_𝓕(p) is
  the number of classes containing a face through p (v and f count the points and faces that I
  touches). On S_G that sum is Σ_{B∈𝒫} |N(B) ∖ B|, the
  vertex-boundary deficiency.
- **(M3) The three-point merge, special to S_G.** After merging, no body has two neighbours in
  another part. Then |N[B]| = |B| + e(B, V ∖ B), so the vertex-boundary deficiency equals def₂(G).

The equivalent form is the identity max_𝒫 [3(|𝒫| − 1) − Σ_B |N(B) ∖ B|] = def₂(G). The inequality ≥
is trivial; ≤ is the content.

## 1. Verdicts at a glance

| Source (`.refs/`) | Read | Nearest item | Verdict |
|---|---|---|---|
| Jackson–Jordán 2006 TR | pp. 1–23 (all) | Lemma 4.1 (pp. 8–9) and its remark; §8 def(H) (p. 22) | same technique for a different statement (M2's shape, unproved; the easy direction for G*) |
| Jackson–Jordán 2008, *DCG* | pp. 258–278 (all) | Lemma 3.2 (p. 265); §6 (p. 277) | as the TR |
| Whiteley 1996, App. A; §8 | pp. 128–137; §8.1–8.3 (pp. 40–45) | Prop. A.1.1's proof, Prop. A.2.9 (pp. 129, 133); Thm A.1.4 (p. 130) | same technique (M1) for a different statement; §8.3: nothing |
| Crapo–Ryan 1986 | §§1–3 (pp. 34–42), §§8–9 (pp. 52–57), problems and history (pp. 64–65) | p. 40, two nodes on a line sharing two points | nothing |
| Whiteley 1989 | pp. 75–95 (all) | proof of Thm 3.1, (b)→(d) (p. 84); proof of Thm 5.4 (pp. 92–93) | same technique (an M2-like closure) for independence; no rank formula |
| Whiteley 1988 | pp. 237–255 (all) | Thms 4 and 10 (pp. 241, 244) | nothing |
| Tanigawa 2010 (arXiv v2) | §§1–6 (pp. 1–26) | Lemmas 4.1, 4.5 (pp. 11–12); §4.3.1 (pp. 17–18) | related normalizations for a different statement; does not specialize |
| Lovász 1977 | §§2–3 (pp. 45–68); §4 headings | Thm 2.3 (pp. 51–52) | nothing beyond the rank formula; does not specialize |
| Lovász–Yemini 1982 | pp. 91–98 (all) | Thm 1 and its proof (pp. 92, 96) | nothing; does not specialize |
| Crapo 1989 | pp. 213–224 (all) | characteristic, p. 216 | nothing |
| Crapo 1991 | headings and keyword search only | none | nothing (skimmed) |
| *Added:* Jackson–Jordán 2008, *Combinatorica* (2007 preprint) | pp. 3–9 | Thm 3.4 (pp. 8–9) | same technique (M3's conclusion) for a different statement |
| *Added:* Jordán 2016 | parts of §2.1 and §2.3 (pp. 43–49) | Lemma 2.1.2 (p. 43), Thm 2.3.2 (p. 49) | same technique (M1, for the (2,3) count) for a different statement |
| *Added:* Sugihara 1986 | §6.4 (pp. 125–128), §11.5 (pp. 206–213) | Thm 6.3, principal partitions | nothing (skimmed) |

No source states the lemma, its identity, or Whiteley's count evaluated on S_G or on any family of
closed neighbourhoods. No source states a result that specializes to it.

## 2. Jackson–Jordán, the pin-collinear papers

**TR 2006-06** (printed page = pdf page − 1). How they pass from the count to def(G):

- **Upper bound, Lemma 4.1 (pp. 8–9).** "r(G*) ≤ 2(|V| + |P|) − 3 − def(G)". Here G* is the
  body-and-pin bar-joint graph. Proof: take a tight partition Q; "let B*(v) = {v} ∪ E_G(v) … and let
  X_i = ∪_{v∈Q_i} B*(v)", so "Σ|X_i| = |V| + |P| + e_G(Q)", and apply 2|X_i| − 3 to each part. This
  is the grouping by closed bodies, the construction in q1-count's easy direction.
- **The remark after it (p. 9).** "We shall see later, in Corollary 6.12, that equality holds in Lemma
  4.1. (This could also be proved directly using the characterization of the rank function of the
  rigidity matroid of a graph given by Lovász and Yemini [9].)" That direct proof would need a merging
  step, but the paper never writes it. Its statement is the *generic* rank of G*, not the pin-collinear
  one.
- **Equality.** It comes by induction (Thm 6.1, pp. 14–20, Claims 6.2–6.10, with bricks and
  superbricks, Lemma 3.3, p. 8). The partition steps there coarsen tight partitions of def(G) itself,
  to compare deficiencies under the inductive operations: "Q = B₁ − {B₁} ∪ {B}" in Claim 6.5 (p. 15);
  "Q = B₂ − {B₂} ∪ {B₂ ∪ B₁}" in Claim 6.10(b) (p. 19). None of them passes from a cover or an
  incidence partition to def.
- **Thm 7.1 (p. 21)** follows from Thm 6.1 with Lemmas 5.1–5.2. There is no count matroid, and
  "scene" appears only in the titles of the references.
- **§8 (p. 22).** For an identified body-and-pin graph H and a partition 𝓕 of the bodies, "let
  w_𝓕(p) be the number of sets F ∈ 𝓕 for which N_H(p) ∩ F ≠ ∅. Put def_H(𝓕) = 3(|𝓕| − 1) −
  2(Σ_{p∈P}(w_𝓕(p) − 1)) … it is not difficult to show that r(H^BP) = 2(|V| + |P|) − 3 − def(H)."
  No proof is given.

Verdict: the same technique for a different statement. §8's def_H has exactly M2's shape: classes of
bodies, each pin charged for the extra classes it meets. *(Inferred)* With a pin read as a scene point,
N_H(p) as the faces through it and coefficient 1 for 2, it becomes M2's face-grouped deficiency. On S_G
that is Σ_w (w_𝒫(N[w]) − 1) = Σ_B |N(B) ∖ B|. It is an analogue, not a specialization: the matroids
differ (generic identified body-and-pin rigidity, against Whiteley's picture matroid), and no choice
of H turns one count into the other. JJ do not prove it, and M3 has no counterpart there.

*(Inferred)* JJ need no M3 because G* gives every edge its own pin vertex. So Σ|X_i| = |V| + |P| +
e_G(Q) holds for every partition. In S_G all the edges at w share the one point w, so a body w with two
neighbours in another part makes |N[B]| < |B| + e(B, V ∖ B). M3 is exactly the step that merges
these collisions away.

**DCG 2008** (printed page = pdf page + 257). Lemma 3.2 (p. 265) is the TR's Lemma 4.1, with the same
proof and the same remark ("This corollary could also be proved directly using … Lovász and Yemini").
§6 (p. 277) is the TR's §8 word for word: def_H, "not difficult to show", Conjecture 6.1. Theorem 5.13
(p. 276) is the body-and-pin rank at a pin-collinear realization. There is no rod-and-pin framework and
no count matroid. Verdict: as the TR.

## 3. Whiteley 1996: Appendix A and §8

Page numbers are the preprint's own.

- **Prop. A.1.1 (pp. 128–129)** [Lor, WW2]. M_{m,k} on hypergraph edges is a matroid. The proof's
  computation, |V(E₁)| + |V(E₂)| = |V(E₁ ∪ E₂)| + |V(E₁) ∩ V(E₂)| put through the count, is M1 for a
  one-type count.
- **Thm A.1.4 (p. 130)** [We]. This is the rank formula q1-count starts from: "ρ_µ(A) = min(|A|,
  Σ_{i=1}^k µ(X_i) + |A ∩ (S − ∪X_i)|)". The printed formula leaves the range of the X_i implicit.
  Prop. A.3.1's r_f (p. 134) gives it: "minimum over all collections {H_i} of non-empty, disjoint
  subsets of A".
- **Prop. A.2.9 (p. 133).** "If k ≤ −(j − 1)m, then the circuits of M_{m,k}(E) are j-connected." The
  proof is M1's identity with the opposite inequality: if a circuit splits along an overlap of at most
  −k/m vertices, the count does not drop. **Remark A.4.2 (p. 135)** carries this to the partitioned
  counts of §A.4 (which include the picture count |V′| + 3|F′| − 3) "using the minimum m_i".
  *(Inferred)* The weighted version, with overlap measured as Σ m_i |V^i ∩ V^i|, is what M1 needs; it
  is not stated.
- **Prop. A.4.1 (p. 135).** It says the partitioned counts give matroids; that is all.
- **§8.** Theorem 8.1.1 (p. 41), Corollary 8.1.2 (p. 41) and the Picture Theorem 8.3.1 (p. 45) are
  all independence criteria. Remarks 8.3.2–8.3.3 cover the polarity and robustness. Thm 8.2.2's proof
  (p. 43) reads each edge copy of a graph as a two-vertex face: a different structure from S_G, with
  no rank computation.

Verdict: the same technique (M1) for a different statement (circuit connectivity), plus the rank
formula. No evaluation on any family like S_G.

## 4. Crapo–Ryan 1986

Printed page = pdf page + 32. The OCR is unreliable in the French columns, so the English ones were
read.

- **§§2–3 (pp. 36–42).** Their approach to the number of free choices is inclusion–exclusion over
  nodes. P. 40 says, on the line: "For any family E = (A, B) of two nodes, we would expect to find
  r(A) + r(B) − r(A∩B) choices. This works out correctly, in particular, when two nodes on the line
  have at least two points in common: there remain only two choices for the scene."
- **§8 (pp. 52–53).** L(E), the E-lift, and "The central objective of the theory here presented is
  accurately to compute this rank". The text is as in `notes/PencilScenes.md` §2.
- **§9 (pp. 56–57).** The tool is the nerve complex: the characteristic χ(E) = r(A) + r(B) + … −
  r(A∩B) − … "gives an initial estimate of the value of b(E), the rank of the E-lift". Higher Betti
  numbers account for the difference.
- **Open problem 5 (p. 64).** "Use the Mayer–Vietoris sequence to develop an algorithmic approach".

There is no generic-rank formula, no count matroid and no partition; closed neighbourhoods never
appear. P. 40 is the geometric fact that nodes sharing a spanning set act as one node: the scene
analogue of "faces sharing three non-collinear points are coplanar". It is not a count-level merge.
Verdict: nothing.

## 5. Whiteley 1989, §§2–5 (printed page = pdf page + 74)

- **No rank formula for dependent structures.** Thm 3.1 (p. 83), Cor. 3.2 (p. 84), Cor. 3.3 (p. 85)
  and Thm 4.2 (p. 87) are all of independent type: Thm 4.2(ii) reads "i′ ≤ a′ + kb′ − k − m". This
  confirms q1-count §1.
- **Thm 3.1, proof of (b)→(d) (p. 84).** This is a closure argument for independence: "let the
  extension of e be the entire set E_j for some face f_j containing the vertices … If some set E′ has
  e′ > v′ − 3, and we extend each edge to get a set E* then e* > v* − 3, since the extension adds at
  most one vertex for each added edge."
- **Thm 5.4 (pp. 92–93).** The count in (ii) is quantified over body-closed substructures only: "for
  every subset of bodies and induced subgraph of attached joints, 2i′ ≤ 3b′ + 2j′ − 3". The proof
  justifies this by "fill[ing] out this body": "These additions can only maintain or increase any
  failure of the count" (p. 93).

Verdict: the same technique, an M2-like closure under faces or bodies, used for independence. There
is no partition rank and no S_G, and M3 is absent.

**The re-check of Thm 3.1 over every infinite field** (requested; page images of pp. 80–81 and 84
checked). Confirmed: no step uses order, topology or characteristic 0. ℝ enters only in the wording:

- Def. 2.4: "indeterminates x_ij over the reals".
- Def. 3.1: maps into R² and R³.
- P. 82: the picture matroid "If p is a set of algebraically independent numbers over the rationals".
- P. 78: the example of a general picture.

Step by step:

- **Prop. 2.4 (p. 80).** Edmonds' formal polynomial argument. It works in any field.
- **Prop. 2.5 (pp. 80–81).** Counting, plus Prop. 2.4 applied to H with singletons added. Any field.
  As q1-count §5 says, "exactly dimension k" needs e = v − k; what the proof shows is that the kernel
  maps onto K^k at every k vertices.
- **Thm 2.3(b) (p. 81).** The kernel lives over K(Y), an infinite field even when K is finite. Take a
  general 3-dimensional subspace of it; general position is the repair q1-count §5 gives for "a
  three-dimensional solution space". Normalize the third row so that m_3j ≠ 0. The cofactor
  identification needs only that any three columns of M are independent. All of this holds over any
  field.
- **Passing to a picture in K^{2v}.** "Remain independent … in A(H, P) for any general picture": a
  maximal minor is nonzero at M, so it is a nonzero polynomial over the prime field, so it has a
  non-root in K^{2v}. This needs K infinite (*(inferred)*: or large enough).
- **Thm 3.1 (a)⟺(c) (p. 84).** "No three points on a line" and the padding by general points: K
  infinite.
- **(b)⟺(d).** Pure combinatorics.

So the agent's reading in q1-count §5 stands as written.

## 6. Whiteley 1988, Tanigawa 2010, Lovász 1977, Lovász–Yemini 1982

The rank formulas in these four, Lovász's Dilworth truncation (1977 Thm 2.3; LY Thm 3, p. 95;
Tanigawa Thm 2.2 and eqs. (1)–(3), pp. 3–5), all specialize to q1-count's *starting* formula: with g
on I(S_G), r_g(I) = min over partitions of Σ g. None says which partitions are optimal for S_G, so
none specializes to M2 or M3.

- **Whiteley 1988** (printed page = pdf page + 236). Thm 4 (p. 241) and Thm 10 (p. 244) count over
  contracted vertex partitions. Thm 4's sufficiency proof groups vertices by equal motion vectors, a
  different device. P. 248 only quotes LY's cover criterion. Verdict: nothing.
- **Tanigawa 2010.** Normalizations of optimal partitions for his body-rod-bar count:
  - Lemma 4.1 (p. 11): an optimal partition of f∘F "may [be] assume[d]" to consist of whole edge
    classes, F*_i = f∘F′_i.
  - Lemma 4.5(iii) (p. 12): the P-connected components form a minimizer.
  - §4.3.1 (pp. 17–18): "K(N(u)) is P-connected … and hence a P-connected component … contains
    K(N(u))". These are cliques on neighbourhoods, in a different matroid.

  Verdict: related normalizations for a different statement. He never touches S_G.
- **Lovász 1977** (pdf page = printed page + 12; the OCR is garbled in places). Thm 2.1 (p. 49) and
  Thm 2.3 (pp. 51–52). Thm 2.3's proof builds an optimal partition by grouping the flats F according
  to the flat F ∪ Q they span with Q = ∪𝓕 ∩ H. The f′ formula is on p. 62. Verdict: nothing beyond the
  formula.
- **Lovász–Yemini 1982** (printed page = pdf page + 90).
  - Thm 1 (p. 92) is the min over covers by subgraphs: "it would suffice to extend the minimum over …
    edge-disjoint spanning subgraphs".
  - The proof (p. 96) normalizes the other way, by splitting: "the partition N₁, …, N_k minimizing
    the left-hand side is automatically such that the edges corresponding to each N_i form a
    connected graph".
  - Merging covers that share two vertices (thin covers) is not in this paper. Its textbook form is
    Jordán 2016 (§7).

  Verdict: nothing.

## 7. Sources outside the list, found in `.refs/`

- **Jackson–Jordán, "On the rigidity of molecular graphs"** (preprint 2007; printed page = pdf
  page; numbering may differ from *Combinatorica* 28, unchecked). This is the nearest relative of M3.
  - Thm 3.4 (p. 8): for a tight partition 𝒫 of the 3-space molecular deficiency, "Let X_i = P_i ∪
    N_G(P_i)", the closed neighbourhood of each part.
  - Its proof gets "e_G({P_i, P_j}) ≤ 1" from tightness (Lemma 3.2(a), p. 7, cited from their brick
    partitions paper) and concludes "|X_i| = |P_i| + d_G(P_i)".
  - With Lemma 3.1 this gives only the upper bound r(G²) ≤ 3|V| − 6 − def(G) (Thm 4.1, p. 9). The
    reverse inequality is, in 3-space, the molecular conjecture, not a counting step.
  - *(Inferred)* The 2-space analogue holds by the same argument: a tight partition of def₂ has
    e(B, C) ≤ 1, since 3 − 2e < 0 otherwise. It gives M3's conclusion for tight partitions, which is
    the trivial direction.

  Verdict: the same technique for a different statement.
- **Jordán 2016** (printed page = pdf page + 32). The (2,3)-count form of M1 in the project's
  cross-check reference:
  - Lemma 2.1.2 (p. 43): "critical sets … with |X ∩ Y| ≥ 2. Then X ∩ Y and X ∪ Y are also critical".
  - Thin covers (p. 48).
  - Thm 2.3.2 (p. 49): "r(G) = min{val(X) : X is a thin cover of G}", due to LY.

  Verdict: the same technique for a different statement. It is the citable presentation for "parts
  with a large overlap merge".
- **Sugihara 1986** (cite by section). §6.4's Thm 6.3 and Cor. 6.3.1 assume "generically
  reconstructible", that is, independent. §11.5 decomposes by principal partitions. Verdict: nothing
  (skimmed).

## 8. What the published theorems already imply

*(Inferred, from results checked by earlier recons.)* Let G be simple with no isolated vertices and q
a generic picture.

- W89 Thm 3.1 with the rank formula gives rank A(S_G, q) = r_g(I), so dim S(q) = 4|V| − r_g(I).
- Whiteley 1984 Prop. 4.1 identifies S(q) with the motions of P_q (q1-count §6, checked there on
  pp. 282–283; not re-read here). P_q is a generic rod-and-pin framework in JJ's sense: the line of
  body v is x_v X + y_v Y + 1 = 0.
- JJ TR Thm 7.1 then gives dim S(q) = 3 + def₂(G).

Hence r_g(I(S_G)) = 4|V| − 3 − def₂(G). With M2, which is generic, this is the merging lemma's
identity. So the identity is a consequence of published theorems, through a four-link chain that no
source assembles. What none of them contains is the direct counting proof (M3 especially), and with it
the route to the rank that avoids KT and JJ.

## 9. Overall verdict

**A chapter may not call the lemma new without qualification.** As a fact, its identity follows from
JJ TR Thm 7.1 through W84 Prop. 4.1, W89 Thm 3.1 and the Edmonds–Rota formula (§8). As an argument,
it appears in none of the sources read. Its ingredients are standard:

- the union defect of a count (W96 App. A; Jordán 2016 Lemma 2.1.2);
- the face grouping (JJ TR §8 and W89 Thm 5.4, in analogous forms);
- the closed-neighbourhood size |P ∪ N(P)| = |P| + d(P) (JJ molecular Thm 3.4).

The proposed attribution sentence:

> "The identity def₂(G) = max_𝒫 [3(|𝒫| − 1) − Σ_{B∈𝒫} |N(B) ∖ B|] follows from Jackson and
> Jordán's rank of rod-and-pin frameworks [JJ, Thm 7.1 of the 2006 report] through Whiteley's
> correspondence between scenes and plate frameworks [W84, Prop. 4.1], his picture theorem [W89,
> Thm 3.1] and the Edmonds–Rota rank formula. We have not found it stated. The direct merging argument
> below is ours. It merges parts by the union defect of the count, as for thin covers in plane rigidity
> [Lovász–Yemini; see Jordán 2016, Lemma 2.1.2 and Thm 2.3.2]. Its last step is the plane analogue of
> Jackson and Jordán's observation that a part's closed neighbourhood has |P ∪ N(P)| = |P| + d(P) [JJ
> 2008, Thm 3.4]."

(Bib keys: `jacksonJordan2008pin` and `jacksonJordan2008` exist; W84, W89 and Jordán 2016's key
`jordan2016` as in `blueprint/src/bibliography.bib`. W84 and W89 still need entries,
`notes/PencilScenes.md` §2.)

**Open, and who decides.**

- Two unread items could still hold M2 or M3 for the picture count. Neither is in `.refs/`:
  - Berg–Jordán, "Algorithms for graph rigidity and scene analysis", ESA 2003, LNCS 2832, 78–89,
    which computes ranks of these count matroids (cited by Tanigawa 2010 [2]);
  - Imai 1985, *Discrete Appl. Math.* 10, 79–92 (W89 [6]).

  Also unread: White–Whiteley's unpublished 1984 count-matroid preprint (W89 [14]) and Lorea 1979. The
  PI decides whether to fetch them before the chapter's wording is fixed.
- Whether the chapter presents the second derivation at all is the PI's call (§6(b)).
