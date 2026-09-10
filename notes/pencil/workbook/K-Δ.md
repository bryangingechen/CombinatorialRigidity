## §(K-Δ) — the Δ-matroid / orthogonal-matroid literature: **NO HIT, with the reason** (and the two readings it does buy)

Discharges `notes/pencil/strategy.md` §7's single recorded unverified lead —
*does the Δ-matroid / orthogonal-matroid literature (Bouchet and successors)
contain anything bearing on the phase's structural obstruction: combinatorics
that can see a quadric?* Verdict on the dispatch's own bar (a specific theorem,
not a thematic resemblance):

> **NO HIT.** The literature is real, is exactly about "combinatorics that sees a
> quadric", and the *shape* of statement the phase wants genuinely exists in it.
> **Two of its three standing hypotheses fail on the phase's object, and each
> failure is independently fatal.**

- **(M1) The subject's objects are *totally isotropic* subspaces; `V_bc` is
  not one.** A representable orthogonal matroid **is** a maximal isotropic
  subspace of a `2n`-dimensional quadratic space (Jin–Kim, *Orthogonal matroids
  over tracts*, Example 3.29: over a field of char ≠ 2, "a strong or weak
  orthogonal `K`-matroid is the same thing as a maximal isotropic subspace of
  `K²ⁿ` in the usual sense"). `V_bc ⊆ Λ²K⁴ ≅ K⁶` is 3-dimensional — the right
  dimension for `n = 3` — but the Klein Gram on `V_bc` is measured to have
  **rank 3** at all 16 flank splits (§(K-flank) *F5(c)*) and **rank 2** at every
  serial length-3 companion (§(K-pitch) *Step 5*). Never 0. So `V_bc` is not a
  point of `OG(3,6)`, has no Wick/spinor coordinate vector, and carries **no
  Δ-matroid**. Isotropy is an `O(6)`-invariant of `V_bc`, not a choice of frame,
  so this is not a normalisation that can be fixed.
- **(M3) The ground set is `[n] = [3]`, fixed by `dim Λ²K⁴ = 6` — it never grows
  with the graph.** Even granting M1, the Δ-matroid of a maximal isotropic in
  `K⁶` lives on a 3-element ground set: its whole content is which of `2³ = 8`
  subsets are feasible. Nothing for a min-max to count, no subset-indexed family
  over `E(G)`. **This is `pencil/strategy.md` §2.2's ingredient-2 failure
  restated in the target literature's own terms**, and it is the more damaging of
  the two, because it would survive any repair of M1.
- **(M2 — a *pass*, recorded so the verdict is honest.)** The *form* of the
  phase's condition matches the literature exactly. Under (PC-Z) the crux is
  `V_bc ∩ α(a) = 0` **and** `V_bc ∩ β(π_a) = 0` — transversality to two fixed
  maximal isotropic 3-spaces. In the Δ-matroid dictionary, transversality of a
  maximal isotropic to a *coordinate* maximal isotropic is precisely
  non-vanishing of the corresponding Wick coordinate, i.e. membership of the
  corresponding subset in the Δ-matroid (Rincón: `w_{[n]∖S} = ±Pf(A_{S△J})`).
  And the two forbidden spaces are *compatible* with one hyperbolic frame:
  `α(a)` and `β(π_a)` meet in `T` (dim 2), so they sit in opposite families —
  exactly the relation between two coordinate isotropics with `|J △ J'| = 1`.
  **So if `V_bc` were isotropic, (W4) would literally be "two prescribed Wick
  coordinates are nonzero".** The shape fits; the hypothesis does not.

### The dictionary, stated so a successor need not re-derive it

- **Δ-matroid** `(V, F)`, `F ⊆ 2^V` nonempty, with the **symmetric exchange
  axiom**: for all `F₁, F₂ ∈ F` and `x ∈ F₁ △ F₂` there is `y ∈ F₁ △ F₂` with
  `F₁ △ {x,y} ∈ F`. A Δ-matroid whose feasible sets are equicardinal is exactly a
  matroid. Introduced by **Bouchet** (1987) as *symmetric matroids*;
  independently, from distance geometry, by **Dress–Havel** (1986) as *metroids*.
- **Linear / representable Δ-matroid.** `A` skew-symmetric with rows and columns
  indexed by `V`; `S ∈ F` iff the **principal** submatrix `A[S]` is nonsingular.
  (General linear Δ-matroids are *twists* `F △ S` of these.)
- **The geometry.** Row-reduce a maximal isotropic `U ⊆ K^{2n}` to `[I | A]`;
  `U` isotropic ⟺ `A` skew-symmetric. Wick (= spinor) coordinates
  `w_{[n]∖S} = Pf(A_S)`; the pure spinors are cut out by the quadratic **Wick
  relations**, generalising Plücker. `supp(w)` is an even Δ-matroid. **Even
  Δ-matroids = orthogonal matroids = Coxeter matroids of type `D_n`**;
  symplectic matroids are `B_n`/`C_n`; ordinary matroids are `A_n`.

**What the subject supplies is ingredient 3, not ingredient 2.** Against
`pencil/strategy.md` §2.1: the irreducible parameter space is the spinor variety;
min-max theorems exist in quantity (Geelen–Iwata–Murota's linear Δ-matroid
parity, Bouchet–Cunningham's jump systems / bisubmodular polyhedra,
Koana–Wahlström's union and delta-sum); the subset-indexed family
`S ↦ Pf(A_S)` exists but on the **ambient** index `[n]`, never on the graph.

> **The missing ingredient is not "a min-max theorem for quadric conditions" —
> that exists. It is the ground set.** The literature manufactures exchange and
> min-max *for a ground set it is handed*; nothing in it manufactures a
> graph-indexed ground set carrying the Klein condition.

A second, structural way to say the same thing: Coxeter-matroid combinatorics
attaches to a point of `G/P`, a flag variety **of the smaller group**. `Gr(3,6)`
is a flag variety of `GL₆`, not of `SO₆`, and `SO₆` does not act transitively on
it (Witt: the orbits are exactly the strata `rank Q|_V ∈ {0,1,2,3}`). So a
non-isotropic 3-space sits in a space that is **not homogeneous** for the group
preserving `Q`, and its `O(6)`-invariant is a single integer — here `3` (or `2`
on serial chains), already recorded by the workbook and carrying no information
about *which* isotropics it meets. **There is no Coxeter-matroid combinatorics
for it, and the reason is a theorem (Witt), not a gap in the literature.**

### The one honest near-miss — Dress–Havel metroids, and (N1)/(N2)

Reported as a near-miss and priced as new mathematics, not a literature lookup.
Dress–Havel 1986: `V` a metric vector space with bilinear form `B`, `E` a finite
set of vectors, the **discriminant** `d_B(F) := det((B(f,g))_{f,g ∈ F})`, and
`J := { F ⊆ E : d_B(F) ≠ 0 }` — a matroid when `B` is anisotropic, and in general
a **metroid** (Bouchet–Dress–Havel 1992: metroids are a special class of
Δ-matroids).

Instantiate on the phase's data: `V = Λ²K⁴`, `B` = the Klein form, `E` = a set of
hinge/companion lines. The Gram entries are *literally* the workbook's four-point
brackets, by its own pairing dictionary (§(K-Λ) *Standing notation*):
`B(C(uv), C(pq)) = [u,v,p,q]`. Every diagonal entry is `0`, because a line is
Klein-null. And at `ℓ = 3` the escape criterion translates exactly. With
`C₁ = C(bx)`, `C₂ = C(xy)`, `C₃ = C(yc)`, `C_ab = C(ab)`, `C_ac = C(ac)`, the
landed closed form (§(K-pitch) *Step 5*) is
`Q(z) = 2·[x,y,a,b]·[b,x,a,c]·[y,c,a,b]·[x,y,a,c]·[b,x,y,c]`, and term by term

```
[x,y,a,b] = B(C₂, C_ab)   [b,x,a,c] = B(C₁, C_ac)   [y,c,a,b] = B(C₃, C_ab)
[x,y,a,c] = B(C₂, C_ac)   [b,x,y,c] = B(C₁, C₃)
```

Since the diagonal vanishes, `d_B({u,v}) = −B(u,v)²`, so each factor is nonzero
**iff** that pair is feasible in the metroid of `E`.

- **(N1)** At `ℓ = 3`, `Q(z) ≠ 0` ⟺ **five prescribed 2-element subsets are all
  feasible** in the Dress–Havel metroid of `{C₁, C₂, C₃, C_ab, C_ac}` under the
  Klein form — a bona fide Δ-matroid-language form of the escape criterion.
- **(N2)** *(verified by the coordinator against the landed `ℓ = 3` closed form,
  2026-08-05)* The five pairs are exactly the five **diagonals of a pentagon**.
  Taking the closed chain `b–x–y–c–a–b` as a pentagon, the structurally-zero Gram
  entries are its five **sides** — `C₁C₂` (meet at `pt(x)`), `C₂C₃` (at `pt(y)`),
  `C₃C_ac` (at `pt(c)`), `C_ac C_ab` (at `pt(a)`), `C_ab C₁` (at `pt(b)`) — and
  the five brackets of `Q(z)` are, up to sign, its five **diagonals**. So
  **`Q(z) ≠ 0` ⟺ no two non-consecutive edges of the pentagon meet.** That is a
  third, purely incidence-geometric reading of the five brackets, beside
  §(K-pitch) *Step 5*'s monomial and §(K-Λ) *Step 1(i)*'s
  `S ∩ α_a = S ∩ β_{π_a} = 0`, and it explains cleanly why `ℓ = 3` is the easy
  case: there `V_bc = S_P` exactly ((D1)'s proof), so the condition is a pure
  incidence condition on the frame; at `ℓ ≥ 4` the annihilator `λ` enters and it
  stops being one.

**Why this is still a MISS, flatly.** *(a)* The ground set does not grow with the
graph: `E` has 5 elements, and more generally path-sum containment gives
`V_bc ⊆ S_P` with `dim S_P = k`, so the whole crux lives inside a configuration
of size `k + 2` — bounded by the **companion length**, the same cap as (D2),
reached from a different direction. Ingredient 2 is *not* restored. *(b)*
Feasibility is **per-placement** — the metroid is the metroid of a
*configuration*, exactly the per-seed object §(K-pure) *P5* names as the wall.
*(c)* The literature's theorems point the wrong way: greedy, parity min-max,
intersection, union all take a Δ-matroid **as input** and optimise over its
feasible sets, whereas the phase asks whether a *prescribed* set stays feasible
across a *family* of configurations. *(d)* The transfer trap: even the metroid of
the *ambient* line configuration would be an ambient object, and §(K-pure) *P6*'s
`P21` witness is the standing warning that ambient hypotheses do not descend to
the decoration variety.

**The ceiling was real and would have bound.** Even a full HIT could not have
reached **(K-chord)**, which is a question inside the generic 3-dimensional
rigidity matroid `R_3` — a type-`A` object with no quadratic form in sight, and
with no combinatorial characterisation. A HIT would at best have addressed the
pitch side and left (K-chord) where the *State of (K)* map leaves it.

**Cross-check against the prior NO HIT.** The 2026-07-30 rigidity-side hunt
(White–Whiteley, Whiteley, Schulze–Tanigawa, Garamvölgyi — all MISSes) and this
one fail for **complementary** reasons: those authors work with **rank**
conditions, so the Klein quadric is invisible to them by construction (§(K-pure)
*P5*); these authors work with the **quadric** but only for objects *on* it, on a
ground set fixed by the ambient dimension. Between them they bracket the phase's
object: a subspace *off* the quadric, in a space the quadric's group does not act
transitively on, indexed by a graph neither subject indexes. §2.2's diagnosis is
confirmed from the outside.

**One pointer offered as possibly better-targeted literature and explicitly NOT
verified in detail:** `V_bc` is a **three-system of screws**, and the classical
screw-theory literature (Ball's theory of screws; Hunt's and Gibson–Hunt's
classification of screw systems) studies exactly the `O(6)`-geometry of such
systems, including the quadric attached to a three-system. It is geometric rather
than combinatorial and would not supply ingredient 2 either, but it is where the
`Gr(3,6)`-with-a-Klein-form object is a *named classical object* rather than an
ad-hoc one. **Anyone pursuing it must verify every citation from scratch.**

**Confidence verdict: NO HIT — proven-informally as a literature verdict** (M1
and M3 are each checked against a primary source and each independently fatal).
**(N1)/(N2) are derivations, (N2) coordinator-verified against the landed closed
form, neither driver-tested.** They change no gap's status.

**What would change this.** *(i)* A construction making the phase's object
**totally isotropic** — the only canonical isotropics in sight are `α(a)`,
`β(π_a)`, `T` and the hinge lines, none of which is `V_bc`. *(ii)* A
**graph-indexed** ground set carrying the Klein condition — the metroid above is
the only candidate found, and its ground set is capped by the companion length.
*(iii)* A theorem converting "prescribed feasibility across a family of
configurations" into a matroid-theoretic statement about one member; not found,
and the literature's theorems run the other way.

### Sources (every entry verified this pass; verification route noted)

No section numbers are asserted except where quoted from a document actually
read. **Two hallucinated attributions were caught and corrected mid-recon and are
recorded here so they are not re-introduced.**

**Founding Δ-matroid / metroid line.** A. Bouchet, *Greedy algorithm and
symmetric matroids*, Math. Programming **38** (1987) 147–159, DOI
`10.1007/BF02604639` (Springer metadata). — A. W. M. Dress, T. F. Havel, *Some
combinatorial properties of discriminants in metric vector spaces*, Adv. Math.
**62** (1986) 285–312, DOI `10.1016/0001-8708(86)90104-0` (Semantic Scholar
record incl. abstract; Havel's own publication list). — A. Bouchet, A. Dress,
T. Havel, *Δ-matroids and metroids*, Adv. Math. **91** (1992) 136–142, DOI
`10.1016/0001-8708(92)90013-B` (Crossref). — A. Bouchet, *Representability of
Δ-matroids*, in Combinatorics (Eger, 1987), Colloq. Math. Soc. János Bolyai
**52**, North-Holland 1988, 167–182. — A. Bouchet, *Maps and Δ-matroids*,
Discrete Math. **78** (1989) 59–71, DOI `10.1016/0012-365X(89)90161-1`. —
W. Wenzel, *Pfaffian forms and Δ-matroids*, Discrete Math. **115** (1993)
253–266, DOI `10.1016/0012-365X(93)90494-E`.

**Coxeter-matroid framework.** I. M. Gelfand, V. V. Serganova, *Combinatorial
geometries and torus strata on homogeneous compact manifolds*, Russian Math.
Surveys **42** (1987) 133–168, DOI `10.1070/RM1987v042n02ABEH001308`. —
A. V. Borovik, I. M. Gelfand, N. White, *Coxeter Matroids*, Progress in
Mathematics **216**, Birkhäuser 2003, xxii+264 pp., ISBN 0-8176-3764-8, DOI
`10.1007/978-1-4612-2066-4`. — Borovik–Gelfand–White, *Symplectic matroids*,
J. Algebraic Combin. **8** (1998) 235–252. — **A. Vince, N. White**, *Orthogonal
matroids*, J. Algebraic Combin. **13** (2001) 295–315, DOI
`10.1023/A:1011212331779` — *a plausible-looking attribution of this paper to
Borovik–Gelfand–White (or to a "Booth–Borovik–Gelfand–Stone") was checked and is
**wrong**.* — **A. Vince** (single author), *The greedy algorithm and Coxeter
matroids*, J. Algebraic Combin. **11** (2000) 155–178, DOI
`10.1023/A:1008780132748`.

**Isotropic subspaces ↔ Δ-matroids (the load-bearing dictionary).** F. Rincón
(**sole author** — a WebFetch summariser reporting "Rincón, Vinzant, Williams" was
a hallucination, contradicted by the publisher record and the PDF header),
*Isotropical linear spaces and valuated Delta-matroids*, J. Combin. Theory Ser. A
**119** (2012) 14–32, DOI `10.1016/j.jcta.2011.08.001`; extended abstract FPSAC
2011, DMTCS proc. **AO** (2011) 801–812, DOI `10.46298/dmtcs.2954`. — T. Jin,
D. Kim, *Orthogonal matroids over tracts*, Forum of Mathematics Sigma **13**
(2025) e130, arXiv:2303.05353 — **PDF read directly**; the quoted Example 3.29,
the `OG(n,2n)`/Wick-equations paragraph and "orthogonal matroids also coincide
with the class of Coxeter matroids of type `D_n`" are from it. — M. Baker,
T. Jin, *Representability of orthogonal matroids over partial fields*, Algebr.
Comb. **6** (2023) 1301–1311.

**Algorithmic / min-max side.** J. F. Geelen, S. Iwata, K. Murota, *The linear
delta-matroid parity problem*, JCTB **88** (2003) 377–398, DOI
`10.1016/S0095-8956(03)00039-X`. — A. Bouchet, W. H. Cunningham,
*Delta-matroids, jump systems, and bisubmodular polyhedra*, SIAM J. Discrete
Math. **8** (1995) 17–32, DOI `10.1137/S0895480191222926`. — T. Koana,
M. Wahlström, *Faster algorithms on linear delta-matroids*, STACS 2025, LIPIcs
**327**, Art. 62, pp. 62:1–62:19, DOI `10.4230/LIPIcs.STACS.2025.62`; full
version arXiv:2402.11596 — **PDF read directly** (the Δ-matroid / symmetric
exchange / linear Δ-matroid definitions quoted above are from its §1.1).

**Surveys.** I. Moffatt, *Delta-matroids for graph theorists*, in Surveys in
Combinatorics 2019, LMS Lecture Note Ser., Cambridge Univ. Press 2019, 167–220,
DOI `10.1017/9781108649094.007` — **the LNS volume number is deliberately
omitted**: sources disagreed (445 / 446 / 456) and the project's rule is to omit
rather than guess; verify against the printed book before any blueprint cite. —
C. Chun, I. Moffatt, S. D. Noble, R. Rueckriemen, *Matroids, delta-matroids and
embedded graphs*, JCTA **167** (2019) 7–59, DOI `10.1016/j.jcta.2019.02.023`.

**Adjacent / negative evidence.** J. P. S. Kung, *Pfaffian structures and
critical problems in finite symplectic spaces*, Ann. Combin. **1** (1997)
159–172, DOI `10.1007/BF02558472` — the one item whose subject is *avoidance*
conditions in a formed space with combinatorial content, but it is the
Crapo–Rota critical problem over **finite** symplectic spaces, not a genericity
statement in characteristic 0. **MISS**; cited for title/subject only, not read.
— J. Cruickshank, B. Jackson, T. Jordán, S. Tanigawa, *Rigidity of Graphs and
Frameworks: A Matroid Theoretic Approach*, arXiv:2508.11636, to appear in Surveys
in Combinatorics 2026, Cambridge Univ. Press, 42 pp. — the corroborating
negative: **zero occurrences** of each of `delta-matroid`, `∆-matroid`,
`Coxeter`, `symplectic`, `isotropic`, `Klein`, `quadric`, `Pfaffian` (checked
mechanically over the extracted PDF text). The two literatures have not met, and
the survey's authors include three of the four people most likely to have noticed
if they should.

**Classical facts used without a bibliographic pointer**, per the project's
"classical" convention: Witt's theorem and the `O(6)`-orbit classification on
`Gr(3,6)` by `rank Q|_V`; the α/β classification of the Klein quadric's maximal
isotropics (already so cited in the workbook); the Plücker/spinor correspondence;
`deg Gr(3,6) = 42`.
