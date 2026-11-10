# Q1: Whiteley 1989's count on S_G (PENCIL-SCENES recon)

*Banked as delivered by a read-only recon agent on 2026-11-09. The coordinator's spot-checks, and the
corrections they found, are in `notes/PencilScenes.md` §5; read that first.*

Read-only recon, 2026-11-09, for `notes/PencilScenes.md` §5 Q1. Sources were read in the PDFs in
`.refs/` (pypdf text, with the page images checked for every quoted statement of Whiteley 1989).
Page numbers are the printed ones, except for Whiteley 1996, whose numbers are the author's
preprint's own pages (the published version is Contemp. Math. 197, pp. 171–311).

## Verdicts

- **(a) Yes.** On S_G, Whiteley's count matroid has rank exactly **4|V| − 3 − def₂(G)**, for
  every finite simple graph G with at least one vertex. So at a general picture the space of scenes
  has dimension 3 + def₂(G), and so does L(q) when every closed neighbourhood has at least three
  members. This is a second derivation of `thm:pencil-jj-equality`, independent of KT Theorem 5.6
  and of Jackson–Jordán. It needs one step that none of the sources read here states: a short
  merging lemma (§3.3). Without it the rank formula gives a minimum over partitions of the
  *incidences*, and that minimum is not obviously def₂. The identity was checked by brute force on
  all 34,188 graphs tested, with no mismatch (§4).
- **(b) Yes.** Whiteley's proof of Theorem 3.1 works over every infinite field, in every
  characteristic. Read "general picture" as "off a proper Zariski-closed set" (a non-root of a
  nonzero polynomial). His "over the reals" and "algebraically independent over the rationals" are
  one sufficient instance of that, not something the proof uses. Two statements are imprecise as
  printed, and each is repaired in a line (§5). Over GF(1000003) and GF(2¹⁶) the numbers agree with
  those over ℚ (§4).
- **(c) No.** Neither Whiteley 1989 nor Whiteley 1996 §8.3 evaluates the count on S_G (or on any
  closed-neighbourhood structure), and neither links scenes to plane body-and-pin frameworks.
  - Whiteley 1989 Theorem 5.4 covers only the independent case, and its proof goes through the
    k = 2 matroid (parallel redrawings of line configurations), not through scenes.
  - Whiteley 1996 Appendix A has the general rank formula, so the dimension in the dependent case is
    there implicitly for every incidence structure, but it is never worked out.
  - The link to P_q is Whiteley 1984 Proposition 4.1 (§6). That paper is outside Q1's scope, but
    the link was checked on pp. 282–283.

## 1. What the sources say

**Whiteley 1989** (Discrete Comput. Geom. 4, 75–95):

- p. 78, general pictures: "a picture P is a *general picture* if it has the minimum space of
  scenes (solution space) for each hypergraph on the vertices. (For example, if the entries in P
  are algebraically independent numbers over the rationals then P will be general.)"
- p. 82, Definition 3.1: a scene is q: V → R³ and r: F → R³ with r₁q₁ + r₂q₂ + q₃ + r₃ = 0 for each
  incidence. A(S, p) is the i × (v + 3f) matrix, and "If p is a set of algebraically independent
  numbers over the rationals, the independence of rows in A(S, p) defines the *picture matroid* of
  S." (The conjecture displayed on the same page reads "i′ ≤ v′ + 3f′ + 4", a misprint for −4;
  p. 76 has −4.)
- p. 83, **Theorem 3.1**: "For an incidence structure S the following are equivalent: (a) The S is
  independent in the picture matroid. (b) For any nonempty subset I′ of I, i ≤ v′ + 3f′ − 3.
  (c) The derived 4-hypergraph H(S) gives independent rows in A(H(S), p) for general pictures p.
  (d) The derived 4-hypergraph H(S) satisfies e′ ≤ v′ − 3 for all nonempty subsets E′ of edges."
  (The "i" in (b) is printed without its prime.)
- p. 84, proof of (a)⟺(c): "Each scene S(q, r) realizing a picture p reduces to a unique scene
  over H(S)(p). Conversely, each scene over H(S)(p), with p in general position (which will have no
  three points on a line) will extend to a unique set of values for r … Independence of H(S) in
  A(H(S), p) means v − e = d. Independence of S in the picture matroid means v + 3f − i = d."
- p. 84, Corollary 3.2: a general picture is sharp iff i′ ≤ v′ + 3f′ − 4 for every substructure
  with at least two faces.
- p. 85, **Corollary 3.3**: "(a) A general picture S(p) has an affine space of scenes of
  dimension d, almost all sharp, with the first face fixed in the projection plane. (b)
  i = v + 3f − 3 − d and i′ ≤ v′ + 3f′ − 4 for any substructure I′ with at least two faces."
  **This is the independent case only.** Condition (b) implies the count of Theorem 3.1 (b), so I is
  independent and the dimension is v + 3f − i. The dependent case is not stated in the paper. The
  same holds for Theorem 4.2 (p. 87), whose count i′ ≤ a′ + kb′ − k − m is again of independent
  type.
- pp. 80–81, the engine: Definition 2.4 (T(H, X), "an e × v matrix X of indeterminates x_ij over
  the reals"); Proposition 2.4 (Edmonds: rows of T independent iff e′ ≤ v′ on all subsets);
  Proposition 2.5; and the proof of Theorem 2.3(b), which uses a 3 × v kernel basis M of T(H, Y) and
  then "These values of y_ij give the corresponding row of the matrix A(H, M), a specialization of
  A(H, X). Since these rows are independent in T(H, Y), they remain independent in A(H, M) and in
  A(H, P) for any general picture."
- p. 92, Theorem 5.4, identified body-and-joint frameworks: an *independent (isostatic)*
  realization ⟺ 2i ≤ 3b + 2j − 3 on every subset of bodies ⟺ such a realization with each body's
  joints collinear. Proof of (ii)→(iii), pp. 92–93: each body is replaced by a line of joints plus
  an extra joint (the incidence graph G°), and then Corollary 5.3 (p. 90) is applied. That
  corollary rests on Theorems 5.1/5.2 at k = 2, which are about parallel redrawings, not scenes.
  Pp. 93–94 state the 3-space analogue as a conjecture: "the methods used here do not extend".

**Whiteley 1996** (`whiteley1996`, preprint pages):

- p. 45, "Picture Theorem 8.3.1 [Wh8]" ([Wh8] = Whiteley 1989): "The incidences I are independent
  in the generic d-lifting matroid if and only if subsets I′ ≠ ∅, |I′| ≤ |V′| + d|F′| − d", plus
  the sharp-lifting criterion. Remark 8.3.2 gives the polarity S ↔ S\* about the paraboloid, and
  Remark 8.3.3 the numerical robustness. There are no frameworks in §8.3.
- p. 41 (§8.1): "Because this generic d-parallel matroid is combinatorially characterized by these
  'submodular counts' (see the §A.1, §A.4), the basic plane results generalize: 1. there are
  efficient algorithms for independence, dependence, rank etc."
- p. 130, "Submodular Theorem A.1.4 [We]" (Welsh 1976): for μ submodular and nonnegative on
  nonempty sets, I(μ) = {A : |A ∩ Y| ≤ μ(Y), Y ≠ ∅} is a matroid with rank
  "ρ_μ(A) = min(|A|, Σᵢ μ(Xᵢ) + |A ∩ (S − ∪Xᵢ)|)".
- pp. 134–135, Proposition A.4.1: counts Σ mᵢ|Vⁱ(E)| + k on partitioned vertex sets give
  matroids, and "This result applies to the counts in the Parallel d-Scene Theorem of §8". The
  picture count |V′| + 3|F′| − 3 is a case of it.

**The rank formula** (used in §3):

- Schrijver, *Combinatorial Optimization* Vol. B: §44.6a, p. 775, "(this result was announced by
  Edmonds and Rota [1966] and proved by Pym and Perfect [1970])"; the rank formula (44.45),
  p. 776, for nondecreasing integer submodular f with f(∅) = 0; and §48.2, pp. 821–822, the
  Dilworth truncation f̂ (48.7), whose submodularity is Theorem 48.2 (Dunstan 1976).
- Tanigawa 2010 (arXiv:1010.5699v2), p. 4, eq. (3), states the combined form for monotone
  submodular μ and cites "[28, Section 44.6a]".

**Jackson–Jordán** (EGRES TR 2006-06, the `.refs/` copy of `jacksonJordan2008pin`):

- p. 21, Theorem 7.2: "(a) r_BP(G) = 3|V| − 3 − def(G). (b) There exists a body-and-pin framework
  (G, q) such that r_BP(G) = 3|V| − 3 − def(G) and, for each v ∈ V, the sets of points
  {q(e) : e ∈ E_G(v)} are collinear."
- p. 22, Theorem 7.4 = "[19, Theorem 5.4]" (Whiteley 1989), re-derived. §8 cites Whiteley 1989
  only for Theorem 5.4 and the p. 93 conjecture. There is no mention of scenes.

## 2. Set-up: S_G, its scene matrix, and L(q)

- **Incidences.** I = D ∪ Ē. Here D = {(v, v)} holds the |V| diagonal incidences, and Ē holds the
  2|E| ordered pairs (u on face v) for uv ∈ E. So |I| = 2|E| + |V|.
- **Scene matrix.** Whiteley's row for (w on face v) is z_w − a_v x_w − b_v y_w − c_v = 0, with
  (a, b, c) = −(r₁, r₂, r₃). The space of scenes S(q) has dimension 4|V| − rank A(S_G, q).
- **S(q) ≅ F(q) at every picture.** Project S(q) onto the planes h_v. The map is injective, since
  z_v = h_v(q_v) by the diagonal incidence. Its image is exactly {h : h_u(q_u) = h_v(q_u) and
  h_u(q_v) = h_v(q_v) for uv ∈ E}, which is F(q). This is Whiteley 1984 §4.1's elimination of the
  heights, at S_G.
- **F(q) ≅ L(q) at admissible pictures.** This is `lem:pencil-lifting-planes-dim`.

So dim L(q) = 4|V| − rank A(S_G, q) at an admissible picture.

## 3. The rank of the count matroid on S_G

### 3.1 The count matroid and its rank formula

Let g(X) = |A(X)| + 3|B(X)| − 3 for X ⊆ I, where A(X) is the set of points and B(X) the set of
faces that X touches. Then g is integer, nondecreasing and submodular (|A(·)| and |B(·)| are
coverage functions), and g(∅) = −3. Whiteley's matroid M_g has independent sets
{F : |X| ≤ g(X) for all nonempty X ⊆ F}.

**Rank formula** (Edmonds–Rota; Pym–Perfect; Schrijver (44.45) applied to the Dilworth truncation
ĝ of (48.7); Tanigawa 2010 eq. (3); Whiteley 1996 Theorem A.1.4):

    r_g(U) = min { |U₀| + Σᵢ g(Xᵢ) : U₀ ⊆ U, {Xᵢ} a partition of U ∖ U₀ into nonempty parts }.

How the pieces fit:

- The independent sets of M_g are those of the matroid of ĝ. Indeed, |X| ≤ g(X) on nonempty X
  holds iff |X| ≤ ĝ(X) on all X, since |X| = Σ|P| ≤ Σ g(P) over any partition.
- ĝ is submodular (Schrijver Theorem 48.2), nondecreasing and integer, with ĝ(∅) = 0, so (44.45)
  applies.
- A single incidence has g = 1 + 3 − 3 = 1, so U₀ can be absorbed as singleton parts:
  **r_g(I) = min over partitions 𝒳 of I of Σ_{X∈𝒳} g(X).**

The direction "≤" is elementary. For F independent, |F| = Σ|F ∩ X| ≤ Σ g(X), using monotonicity,
and g ≥ 1 on nonempty sets. The direction "≥" is the theorem.

### 3.2 Whiteley's theorem turns this into a dimension

By Theorem 3.1, applied to the substructure that each F ⊆ I spans, the generic picture matroid of
S_G is M_g. So at a general picture, rank A(S_G, q) = r_g(I) and dim S(q) = 4|V| − r_g(I).

### 3.3 The merging lemma (the agent's derivation; not found in any source read)

For X, Y ⊆ I:

    g(X ∪ Y) = g(X) + g(Y) + 3 − |A(X) ∩ A(Y)| − 3|B(X) ∩ B(Y)|

This is exact, since A(X ∪ Y) = A(X) ∪ A(Y) and B(X ∪ Y) = B(X) ∪ B(Y). So merging two parts does
not raise the sum when they **share a face**, or when they **share at least three points**.

Take an optimal partition of I and merge such pairs until none is left. Each merge lowers the
number of parts and does not raise the sum, so the result is still optimal, and it has two
properties:

1. **Its face sets partition V.** They are pairwise disjoint, and every face v occurs, through
   (v, v). Write P for this partition of V. The part X_B with face set B ∈ P contains every
   incidence on a face of B, so A(X_B) = N[B] and g(X_B) = |N[B]| + 3|B| − 3.
2. **No vertex has two neighbours in a foreign part.** Suppose w ∈ C had neighbours u₁ ≠ u₂ in
   B ≠ C (they are distinct because G is simple). Then w, u₁ and u₂ all lie in N[B] ∩ N[C]:
   w ∈ C ⊆ N[C], w is adjacent to B, the uᵢ lie in B, and the uᵢ are adjacent to w ∈ C. That
   makes three shared points, so the pair would have been merged.

By property 2, |N[B]| = |B| + e(B, V ∖ B) for every B ∈ P, and so

    r_g(I) = Σ_{B∈P} (4|B| − 3 + e(B, V∖B)) = 4|V| − 3|P| + 2 d_G(P) ≥ 4|V| − 3 − def₂(G).

Conversely, every partition P of V gives the face-grouped partition {X_B} of I, whose sum is
4|V| − 3|P| + Σ_B |N(B) ∖ B| ≤ 4|V| − 3|P| + 2d_G(P). Hence:

> **Theorem.** For every finite simple graph G with V ≠ ∅, r_g(I(S_G)) = 4|V| − 3 − def₂(G).
> Equivalently, the vertex-boundary deficiency max_P [3(|P| − 1) − Σ_{B∈P} |N(B) ∖ B|] equals
> def₂(G).

What the proof uses and what it does not:

- **Hypotheses.** Simplicity is used in property 2. Degrees are not used: the identity holds with
  leaves and isolated vertices too, as the §4 sweep confirms.
- **The merge is really needed.** Take two K₄'s and a hub w adjacent to two vertices of each.
  The partition {K₄, K₄, {w}} attains the vertex-boundary value 0 = def₂, but its edge value is
  −2. In 126 of the 240 random graphs on 7–8 vertices, some optimal vertex-boundary partition
  likewise needs the merge.
- **Scope.** This computes the rank of the whole incidence set, not an isomorphism of matroids. The
  argument does not show that M_g contracted by D is the union of three graphic matroids on 2G, and
  that was not checked.

### 3.4 Consequence

At a general picture, dim S(q) = dim F(q) = 3 + def₂(G) for every simple G. With
`lem:pencil-lifting-planes-dim`, dim L(q) = 3 + def₂(G) when every closed neighbourhood has at
least three members, which is `thm:pencil-jj-equality`. With `lem:pencil-lifting-planes-motions`,
rank R(P_q) = 3|V| − 3 − def₂(G): the value of JJ Theorem 7.2, for simple G.

The route uses no KT and no JJ. It uses Whiteley 1989 Theorem 3.1, the Edmonds–Rota/Dilworth rank
formula, and §3.3. Formalizing it would mean formalizing Whiteley 1989 §§2–3 and the rank formula.
The KT route is already in Lean, so this route is a matter of attribution and exposition, not a
proof change.

## 4. Numerical check (exact arithmetic)

The scripts are banked byte-identical as `notes/scripts/scenes/q1_count.py` and
`notes/scripts/scenes/q1_sweep.py`; their invocations are in `notes/scripts/README.md` §3 (`scenes/`).

What `q1_count.py` computes:

- **def2.** Enumerated over all partitions of V.
- **defvb.** The vertex-boundary deficiency.
- **rcount.** The rank of M_g, by the greedy algorithm with an exact oracle that does not use the
  partition formula. F is independent iff, for every nonempty face set B′,
  Σ_a max(0, c_a(B′) − 1) ≤ 3(|B′| − 1), where c_a(B′) counts the incidences of F with point a on
  a face of B′. Two incidence orders were run and agree.
- **dim L.** The kernel dimension of Whiteley's scene matrix at random admissible pictures (integers
  in [−10⁶, 10⁶]), asserted equal to the directly computed dim L(q). This was done over ℚ
  (`fractions`), over GF(1000003), and over GF(2¹⁶) (irreducibility of the modulus checked in the
  script).

Seed 20261109, Python 3.15, about 2 s. The output is byte-identical on rerun.

| graph | n | E | I | def2 | defvb | 4n − rcount | 3 + def2 | dim L, ℚ (3 pictures) | dim L, GF(1000003) | dim L, GF(2¹⁶) | agree |
|---|---|---|---|---|---|---|---|---|---|---|---|
| C4 | 4 | 4 | 12 | 1 | 1 | 4 | 4 | 4,4,4 | 4,4 | 4,4 | yes |
| C5 | 5 | 5 | 15 | 2 | 2 | 5 | 5 | 5,5,5 | 5,5 | 5,5 | yes |
| C6 | 6 | 6 | 18 | 3 | 3 | 6 | 6 | 6,6,6 | 6,6 | 6,6 | yes |
| K4 | 4 | 6 | 16 | 0 | 0 | 3 | 3 | 3,3,3 | 3,3 | 3,3 | yes |
| K5 | 5 | 10 | 25 | 0 | 0 | 3 | 3 | 3,3,3 | 3,3 | 3,3 | yes |
| K2,3 = θ(2,2,2) | 5 | 6 | 17 | 0 | 0 | 3 | 3 | 3,3,3 | 3,3 | 3,3 | yes |
| K2,4 | 6 | 8 | 22 | 0 | 0 | 3 | 3 | 3,3,3 | 3,3 | 3,3 | yes |
| K3,3 | 6 | 9 | 24 | 0 | 0 | 3 | 3 | 3,3,3 | 3,3 | 3,3 | yes |
| diamond = θ(1,2,2) | 4 | 5 | 14 | 0 | 0 | 3 | 3 | 3,3,3 | 3,3 | 3,3 | yes |
| θ(1,2,3) | 5 | 6 | 17 | 0 | 0 | 3 | 3 | 3,3,3 | 3,3 | 3,3 | yes |
| θ(1,3,3) | 6 | 7 | 20 | 1 | 1 | 4 | 4 | 4,4,4 | 4,4 | 4,4 | yes |
| θ(2,2,3) | 6 | 7 | 20 | 1 | 1 | 4 | 4 | 4,4,4 | 4,4 | 4,4 | yes |
| θ(2,3,3) | 7 | 8 | 23 | 2 | 2 | 5 | 5 | 5,5,5 | 5,5 | 5,5 | yes |
| θ(3,3,3) | 8 | 9 | 26 | 3 | 3 | 6 | 6 | 6,6,6 | 6,6 | 6,6 | yes |
| θ(2,2,2,2) | 6 | 8 | 22 | 0 | 0 | 3 | 3 | 3,3,3 | 3,3 | 3,3 | yes |
| triangular prism | 6 | 9 | 24 | 0 | 0 | 3 | 3 | 3,3,3 | 3,3 | 3,3 | yes |
| bowtie | 5 | 6 | 17 | 0 | 0 | 3 | 3 | 3,3,3 | 3,3 | 3,3 | yes |
| wheel W5 | 6 | 10 | 26 | 0 | 0 | 3 | 3 | 3,3,3 | 3,3 | 3,3 | yes |
| K4, one edge subdivided | 5 | 7 | 19 | 0 | 0 | 3 | 3 | 3,3,3 | 3,3 | 3,3 | yes |
| two K4 at a vertex | 7 | 12 | 31 | 0 | 0 | 3 | 3 | 3,3,3 | 3,3 | 3,3 | yes |
| octahedron | 6 | 12 | 30 | 0 | 0 | 3 | 3 | 3,3,3 | 3,3 | 3,3 | yes |
| cube Q3 | 8 | 12 | 32 | 0 | 0 | 3 | 3 | 3,3,3 | 3,3 | 3,3 | yes |
| Petersen | 10 | 15 | 40 | 0 | 0 | 3 | 3 | 3,3,3 | 3,3 | 3,3 | yes |
| random1, n=6, E=[(0,1),(0,3),(0,4),(0,5),(1,4),(1,5),(2,3),(2,5)] | 6 | 8 | 22 | 0 | 0 | 3 | 3 | 3,3,3 | 3,3 | 3,3 | yes |
| random2, n=7, E=[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(1,3),(1,4),(1,6),(2,3),(2,4),(2,6),(3,5),(3,6),(4,5),(4,6),(5,6)] | 7 | 18 | 43 | 0 | 0 | 3 | 3 | 3,3,3 | 3,3 | 3,3 | yes |
| random3, n=7, E=[(0,1),(0,3),(0,4),(0,6),(1,2),(1,5),(2,3),(2,6),(3,4),(3,5),(5,6)] | 7 | 11 | 29 | 0 | 0 | 3 | 3 | 3,3,3 | 3,3 | 3,3 | yes |
| random4, n=8, E=[(0,2),(0,7),(1,2),(1,5),(3,5),(3,6),(3,7),(4,6),(4,7)] | 8 | 9 | 26 | 3 | 3 | 6 | 6 | 6,6,6 | 6,6 | 6,6 | yes |
| random5, n=8, E=[(0,1),(0,2),(0,4),(1,2),(1,5),(2,3),(2,4),(2,5),(2,6),(3,6),(4,5),(4,7),(6,7)] | 8 | 13 | 34 | 0 | 0 | 3 | 3 | 3,3,3 | 3,3 | 3,3 | yes |
| random6, n=9, E=[(0,1),(0,4),(1,2),(1,3),(1,4),(2,3),(2,6),(3,5),(3,6),(3,7),(3,8),(4,5),(4,6),(4,8),(5,6),(5,7),(6,8),(7,8)] | 9 | 18 | 45 | 0 | 0 | 3 | 3 | 3,3,3 | 3,3 | 3,3 | yes |
| random7, n=9, E=[(0,3),(0,5),(0,6),(0,7),(1,4),(1,6),(1,8),(2,3),(2,4),(2,8),(3,4),(3,5),(3,8),(4,6),(4,7),(5,8),(6,8)] | 9 | 17 | 43 | 0 | 0 | 3 | 3 | 3,3,3 | 3,3 | 3,3 | yes |

θ(a, b, c) is two poles joined by internally disjoint paths with a, b and c edges.

**The sweep (`q1_sweep.py`, seed 1109, about 34 s)** checks the identities defvb = def2 and
4n − rcount = 3 + def2 on 34,188 simple graphs, with **no mismatch**:

- every labelled simple graph on n ≤ 6 vertices (33,867 graphs, any degrees, isolated vertices
  included);
- 320 random graphs on 7–10 vertices;
- the two-K₄-and-hub graph.

On 81 of them it also compared the dimension of the scene space at a random rational picture with
3 + def2, and with dim L(q) when the minimum degree is at least 2. All agree.

Which S_G are independent: S_G is independent iff 2|E| + |V| = 4|V| − 3 − def₂, that is, iff the
partition into singletons attains def₂. Examples are the cycles, θ(3,3,3) and random4 (|I| = 26
there). Only for these does Corollary 3.3's independent count apply.

## 5. (b) Over every infinite field

Each step of Whiteley's proof, and what it needs (K infinite, of any characteristic):

| Step | What it uses | Field |
|---|---|---|
| Prop. 2.4 (Edmonds) | a polynomial identity in distinct indeterminates; each matching term has coefficient ±1 | any field |
| Prop. 2.5 | counting plus Prop. 2.4 on H with singletons added | any field |
| Thm 2.3(a), and the necessity in Thm 3.1 | the 3-dimensional trivial scenes (affine functions) | any field |
| Thm 2.3(b) | kernel of T(H, Y) over K(Y); cofactors; normalizing M's third row to 1 needs a combination of rows with no zero entry | infinite field |
| from one picture to general pictures | some maximal minor of A(H, ·) is nonzero at one picture over K(Y), so it is a nonzero polynomial over the prime field, so it has a non-root in K^{2v} | infinite K |
| Thm 3.1 (b)⟺(d) | pure combinatorics | none |
| Thm 3.1 (a)⟺(c), the padding | no three points of a face collinear (Zariski-open); extra vertices placed at general points | infinite field |
| Cor. 3.2 | a combination of scenes avoiding finitely many proper subspaces | infinite field |

Nothing in the proof uses order, topology or characteristic 0. Over a countable field such as ℚ,
no algebraically independent picture exists, but Zariski-general pictures do, so "general" should
be read in the Zariski sense.

Two statements are imprecise as printed (p. 80, p. 81):

- **Proposition 2.5** says "a solution space of *exactly* dimension k". That holds only when
  e = v − k, which is what its proof assumes.
- **Theorem 2.3(b)** says "a three-dimensional solution space", which again needs e = v − 3.

Repair: use a general 3-dimensional subspace of the kernel. The kernel maps onto K³ at every
triple of vertices (this is Proposition 2.5's singleton argument), so a general subspace does too.
The proof then goes through unchanged.

## 6. (c) The body-and-pin link

What the sources contain:

- **Whiteley 1989** reaches body-and-joint frameworks only in §5.3 (Definition 5.4, p. 91), at
  k = 2, and only for independent realizations (Theorem 5.4, p. 92).
- **Whiteley 1996 §8.3** has no frameworks.
- **Neither paper** evaluates the count on S_G.
- **Whiteley 1996 Appendix A** (Theorem A.1.4 with Proposition A.4.1) gives the rank, and so the
  dimension of liftings in the dependent case, for every incidence structure. It is never worked
  out for a family like S_G.
- **JJ** cite Whiteley 1989 only for Theorem 5.4 (their Theorem 7.4) and the p. 93 conjecture.

What would make the equality a corollary of Whiteley's work:

- **Whiteley 1984, Proposition 4.1** (p. 282): "there is an isomorphism between the scenes S(q, r)
  over the picture and the instantaneous motions M of the reduced plate framework". In its row
  reduction, the incidences at a vertex w create "a fan of k − 1 bars along the same line
  (x_w, y_w, 1)". The fan runs from the first face at w. Order (w, w) first, and the fan becomes
  the star from plate w. Each edge uw then gets two bars, on ℓ_u and ℓ_w, which is a pin at
  ℓ_u ∩ ℓ_w. That framework is P_q, and it is pin-collinear. P. 283 notes that other orderings give
  line-equivalent frameworks.
- **The chain.** Whiteley 1984 Prop. 4.1, plus 1989 Theorem 3.1, plus the rank formula, plus §3.3,
  gives the pin-collinear rank 3|V| − 3 − def₂ for simple G. The one missing link is the §3.3
  evaluation, which is elementary but stated in none of these papers.

## 7. Corrections to the planning note's leads

- **§2, the Whiteley 1989 entry.** "Corollaries 3.2–3.3: … the dimension of the space of scenes"
  should add "in the independent case". The dimension in the dependent case needs the rank formula,
  which is in Whiteley 1996 Appendix A and Schrijver §44.6a / §48.2, not in Whiteley 1989.
- **§2, the Whiteley 1996 entry.** The Picture Theorem 8.3.1 is on preprint p. 45 (§8.3 begins on
  p. 43), and Appendix A.1 is on pp. 128–130.
- **§3, the `thm:pencil-jj-equality` row.** "the generic scene dimension of S_G, which Whiteley
  1989 Thm 3.1 counts (Q1)" is confirmed, with §3.3 as the step the sources lack.

## Open, and who decides

- **Whether a chapter states this second derivation.** It would cite Whiteley 1984 Prop. 4.1,
  Whiteley 1989 Theorem 3.1, the rank formula, and the merging lemma as the project's own step. This
  is the PI's call at the open (§6 (a)/(b)).
- **The merging lemma's provenance.** No source read states it. Before any chapter calls it new, it
  should go through the Q3/Q4 search; Sugihara 1986 and Imai 1985 are the likely places.
- **Formalizing this route** is not needed: the KT route is in Lean.
