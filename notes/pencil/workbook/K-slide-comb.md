## §(K-slide-comb) — the combinatorial residue: **refuted as stated**, and the packing half made uniform

Sibling of §(K-slide-cl), settling the residue its Step C5 named. Standing
notation inherited (`G°`, lengths `ℓ`, split edge `e₀ = bc` of length 3, the
six basis lines `L_ij` of the coordinate tetrahedron, the classes `E_L`, the
menus `A_P`, witnesses (W1)–(W4)). Throughout `n = |V°|` and
`E° = E(G°) ∖ {e₀}`; **class shape** means exactly what the §(K-slide)
battery certifies — `G°` simple with min degree ≥ 3, the subdivision `G`
tight (`def = 0`, hence 5/6-sparse on every subgraph) and `hnoRigid`, both
`e₀`-ends hubs.

> **Label scoping.** The `(C…)` labels below continue §(K-slide-cl)'s
> `(C0)`–`(C5)` run, so this section's **(C6)** (the unrestricted packing) and
> **(C7)** (the length-4 menu repair) belong to the *collapse* family. They are
> unrelated to the identically-numbered **(C7)/(C8)** of
> `notes/Pencil-W4-informal.md` §(SAFE-RES) / §`hnoGood'`
> vacuity, which are the *W4 residual structure theorem*'s claims — the ones the
> route-3(b) adjudication is pinned on. Cite either by section, never by bare
> number.

**Verdict (2026-08-05, fifth pass).**

(i) **(K-slide-comb) is REFUTED as a class statement**, at two *structural*
flanks — both exhibited at explicit class members with **all lengths in
`{3,4}`**, so `G` is triangle-free with singleton closed hub-neighbourhoods
and the `hcard`/`htf` side conditions the (K) consumer carries
(`hasGenericPencilRealization_of_independent_pencilRow_target`,
`Escape.lean:186`) hold outright — read off `Graph.closedHubNbhd`'s body
(`Motive.lean:82`: the *pencil hubs* among `v` and its neighbours): with every
`ℓ ≥ 3`, a hub's neighbours are all degree-2 interiors, so
`closedHubNbhd u = {u}`, an interior's is at most its two hub neighbours, and
the girth is `≥ 6`:

- **the 5-chromatic flank (robust).** `G° = K5` with lengths
  `(3,3,3,3,4,4,4,4,4,4)` is tight + `hnoRigid` (`|V| = 31`; 84 of the
  all-`{3,4}` assignments qualify **under this section's convention** — the
  count is convention-dependent, reconciled 2026-08-05 in §(K-flank) *F1*:
  **210** = `C(10,4)` all-`{3,4}` assignments with `Σℓ = 36` are class shapes,
  every one of them, `hnoRigid` never failing here; **84** = `C(9,3)` of those
  have the *designated* split edge `(0,1)` at length 3, which is what
  `kslidecomb.py` counts, while `flanks.py --strata` takes `e₀` := the first
  length-3 edge — as `--k4full` does — and so reports all 210. Both figures are
  right under their own convention), and `χ(K5) = 5`. A **proper** colouring
  is forced for *any* tetrahedral decoration, not merely for the (C2)
  dictionary: if `pt(u) = pt(w)` on a hub path of length `ℓ`, its (S2) limit
  chain spans `< ℓ` (machine-checked at every `ℓ ∈ {1,…,5}`; at `ℓ ∈ {1,3}`
  the chord is `0`), so by the serial-chain count of §(K-slide) Step 5 the
  path carries a stress and (W1) fails. Hubs live at four points, so
  `χ(G°) ≤ 4` is *necessary* — and it fails in the class. (By **Brooks'
  theorem**, `χ(G°) ≥ 5` forces `G° = K5` or `Δ(G°) ≥ 5`, so this flank is
  exactly characterised.)
- **the acyclicity flank.** Every menu of (C2)/(C4) contains
  `L_{φu, φw}`, so `E_{L_ij}` contains **all** of `E°`'s `{i,j}`-coloured
  edges; since every class must be a forest, `φ` must be an **acyclic**
  colouring — every bicoloured subgraph a forest — not merely proper.
  Among the 23 hub graphs with `|V°| ≤ 6` (simple, connected, min degree
  ≥ 3), four are 4-colourable but have **no** acyclic 4-colouring; the
  6-vertex 11-edge one carries all-`{3,4}` tight + `hnoRigid` lengths
  (`|V| = 31`) and admits no admissible `φ` **even after `e₀` is deleted**
  (deleting `e₀` does rescue one of the four — the octahedron, whose separate
  and deeper failure is Step D3 — but not this one). So
  Step C5's "proven piece" (5/6-sparsity ⟹ 3-degeneracy ⟹ greedy
  4-colouring) does **not** discharge the colouring premise: *proper* is the
  wrong invariant, and acyclic 4-colourability is not implied by
  3-degeneracy. (Acyclic colouring in **Grünbaum**'s sense — *Acyclic
  colorings of planar graphs*, Israel J. Math. **14** (1973) 390–408,
  DOI 10.1007/BF02764716.)

(ii) **The packing half is uniform and proven — (C6).** Strip the menus and
ask only for the packing: assign each `P ∈ E°` a set of `6 − ℓ_P` of the six
labels so that three classes are spanning trees of `G° − e₀` and three are
2-component forests separating `b` from `c`. Equivalently: **three bases of
`M(G°)/e₀` plus three bases of `M(G°) ∖ e₀`, with `P` used `6 − ℓ_P` times.**
This is a matroid-union / base-packing question, and **Edmonds' matroid-
partition min-max hypothesis for it is exactly 5/6-sparsity of `G`** — so it
holds at **every** class shape (Step D1; proof below, and the min-max
inequality plus an explicit packing re-verified at every shape any driver
touches — 877 exhaustive `K4` + 48 sweep + 7 battery + the flanks). The
forest/separator structure is therefore *never* the obstruction;
the menu is. This also settles the second sub-question Step C5 posed: yes,
matroid-flavoured — but the constrained problem is matroid **intersection**,
not union (Step D2).

(iii) **(C2)'s length-4 entry is not "forced" — a correction.** With the free
middle placed generically in a face plane `π(i,j,k)` and one end's pencil line
confined to that plane, `R_P = ⟨L_ij, L_xk⟩` for either `x ∈ {i,j}` — 12/12
exact witnesses. So the length-4 menu is **all five** 2-subsets containing
`L_ij`, not just `{L_ij, L_opp(ij)}`. That repair alone lifts the exhaustive
`G° = K4` coverage from **439/877 to 702/877** and **rescues** the third
(non-structural) flank below. It is the natural continuation, named **(C7)**.

(iv) **Coverage, measured.** Menu-solvability of the pure dictionary is far
from class-wide even where the colouring premise holds: on the exhaustive
`G° = K4` stratum, **439 of 877** class shapes solve — and all **438**
failures have a satisfiable colouring premise, so at `K4` the obstruction is
purely the menu. On the `|V°| ≤ 5` sweep, 18/48. The seven §(K-slide) battery
members all solve (control, 7/7), and the *only* all-lengths-`≥ 3` `K4` shape
is `(3,3,3,3,3,3)` — tightness forces it — which solves. So the tetrahedral
collapse covers a neighbourhood of the all-length-3 stratum
(`|E°| + 1 = 2n − 2`) and thins out as `G°` densifies, because tightness
(`Σℓ = 6(m − n + 1)`) then forces long paths, whose menus are smallest.

**Consequence for (K-slide-cl).** The implication "(K-slide-comb) ⟹
(K-slide-cl) at that shape" is untouched and still proven; what changes is
that its antecedent is now **known false** at explicit class members. So
(K-slide-cl) reverts to **open**, with the covered sub-class named
(every shape where the assignment problem — pure or (C7)-repaired — is
solvable, including all 7 battery members and hence the `K4`/`W4` control
habitats) and the uncovered flanks located (`χ(G°) ≥ 5`; no acyclic
4-colouring; plus the residual menu failures).

**What would change this.** *For the refutation:* an error in class
membership of the exhibited shapes — they are certified by the same
`def = 0` + `hnoRigid` + hub-ends + parallel-free criterion as the battery,
and additionally satisfy `hcard`/`htf`; a genuine further habitat condition
excluding `K5`-shaped or `Δ ≥ 5` hub graphs would blunt the 5-chromatic
flank (none is known — the L7b consumer's conditions are exactly
`hcard`/`htf`, both satisfied). *For (C6):* a class shape whose min-max
inequality fails — impossible by the Step-D1 proof unless 5/6-sparsity
fails, i.e. unless the shape is not tight. *For the route:* a repaired
dictionary (C7) that keeps `L_ij` mandatory can never beat the acyclicity
flank, and no tetrahedral decoration can beat the 5-chromatic flank — so a
class proof needs either a **basis configuration with more than four hub
positions**, or a decoration admitting **non-basis ("extra") rows on long
paths** — the (C4) meet-plane trade, generalized — or it must abandon the
collapse and work with the generic pure condition.

### Step D0 — the residue as pure combinatorics

By Step C0 the hub-level limit system has `6|V°| − 9` rows and edge `P`
contributes `6 − ℓ_P` of them; by (C1) an aligned decoration splits it into
six scalar systems indexed by the basis lines, with `E_L = {P : L ∈ A_P}`.
So the residue is exactly a **multiplicity-weighted 6-fold forest packing of
`G° − e₀` with a per-edge legal menu**:

- **count.** `Σ_{P∈E°}(6 − ℓ_P) = 6(m−1) − (Σ_{E(G°)}ℓ − 3) = 6n − 9`
  using tightness `Σℓ = 6(m − n + 1)`, matching Step C0's row count exactly.
- **(W1)** ⟺ every `E_L` is a forest; then `Σ_L (c_L − 1) = 3`.
- **(W2)** ⟺ exactly three classes separate `b` from `c` — which, given the
  excess-3 budget, forces three spanning trees plus three 2-component
  separating forests, and `V_bc = ⟨opp-dual(L) : L separating⟩`.
- **(W4)** ⟺ the separator triple contains an opposite pair (C3); **(W3)/(W4)
  otherwise depend only on the local type**, so they are a finite check, not
  part of the combinatorics (C3).

Two reformulations do the work below. First, a **separating class `E_L` with
`c_L = 2` and `b|c` separated is the same thing as `E_L ∪ {e₀}` being a
spanning tree of `G°`** — i.e. `E_L` is a *base of `M(G°)/e₀`*; a spanning
tree class is a *base of `M(G°) ∖ e₀`*. Sizes check:
`3(n−2) + 3(n−1) = 6n − 9`. Second, the **menu** is what makes the problem
hard, and it is worth naming what it forbids: for `P` coloured `{i,j}`,
`L_ij ∈ A_P` always, and every other member of `A_P` shares a colour with
`{i,j}` **except** `opp(ij)`, which is reachable only at `ℓ ∈ {2 (pt-mode),
4}`. So class `E_{pq}` can only receive edges that *touch* `p` or `q`, plus
`opp(pq)`-coloured edges of length 2 or 4 — the **starvation bound**
computed in Step D3.

### Step D1 — (C6): the packing half is never the obstruction

> **(C6)** *(proven-informally)* — for **every** class shape there exist
> `A_P ⊆ {L_ij}` with `|A_P| = 6 − ℓ_P` such that three classes are bases of
> `M(G°) ∖ e₀` and three are bases of `M(G°)/e₀` (hence 2-component forests
> separating `b|c`), and the three separating labels may be chosen to contain
> an opposite pair.

*Proof.* Take the ground set `Ω` with `6 − ℓ_P` parallel copies of each
`P ∈ E°` (`|Ω| = 6n − 9`) and the six matroids `M₁ = M₂ = M₃ = M(G°)/e₀`,
`M₄ = M₅ = M₆ = M(G°) ∖ e₀` (ranks `n−2`, `n−1`; `G°` is 2-edge-connected on
the stratum, so `G° − e₀` is connected — and the driver's *explicit* packing
re-certifies that shape by shape, since a spanning tree of a disconnected
`G° − e₀` would not exist). By **Edmonds' matroid-partition theorem** the
union has rank
`min_{T ⊆ Ω}(|Ω ∖ T| + Σ_i r_i(T))`, and since each `r_i` depends only on
the support of `T`, the minimum is attained at a union of parallel classes,
i.e. at some `F ⊆ E°`. So `Ω` is partitionable iff

> `Σ_{P∈F}(6 − ℓ_P) ≤ 3·r_{M/e₀}(F) + 3·r_{M∖e₀}(F)` for every `F ⊆ E°`.

Write `W = V(F)`, `k` = number of components of `(W, F)`. Then
`r_{M∖e₀}(F) = |W| − k`, and `r_{M/e₀}(F) = |W| − k` unless `b, c` lie in the
**same** component of `F`, in which case it is `|W| − k − 1`. Now
5/6-sparsity of `G` says, for any branch union `F′` spanning `W′` and
connected, `5·Σ_{F′}ℓ ≤ 6(|W′| + Σ_{F′}(ℓ−1) − 1)`, i.e.

> `Σ_{P∈F′}(6 − ℓ_P) ≤ 6(|W′| − 1)`.

*Case `b ≁ c` in `F`:* sum that over the `k` components — the requirement is
exactly `Σ_F (6−ℓ_P) ≤ 6(|W| − k)`. ✓
*Case `b ∼ c` in `F`,* say in component `F₀` on `W₀`: the requirement carries
an extra `−3`, i.e. `Σ_{F₀}(6−ℓ_P) ≤ 6(|W₀| − 1) − 3`. Apply the sparsity
inequality to `F₀ ∪ {e₀}` — still connected, still spanning `W₀`, and `e₀`
contributes `6 − ℓ_{e₀} = 3`: `Σ_{F₀}(6−ℓ_P) + 3 ≤ 6(|W₀| − 1)`. ✓ (The
`−3` is supplied *exactly* by `ℓ_{e₀} = 3`, the same 3 that is `dim V_bc`.)
Finally, partitioning `Ω` gives six independent sets of total size
`6n − 9 = 3(n−2) + 3(n−1)`, and each part is capped by its matroid's rank —
so every part is a **base**, which is the claim. Two parallel copies of `P`
can never share a part (they are parallel in a graphic matroid), so each `P`
lands in `6 − ℓ_P` *distinct* classes. The label names are ours, so the
separator triple can be any triple containing an opposite pair. ∎

Remarks. **(a)** Only 5/6-sparsity is consumed — not `hnoRigid`, not
parallel-freeness, not the colouring. **(b)** This is the same machinery the
project has landed: Phase 12's vendored matroid union
(`Matroid/Constructions/{Submodular,Union}.lean`), Phase 13's
Tutte–Nash-Williams packing (`BodyBar/TreePacking.lean`), Phase 14's k-fold
cycle-matroid union (`BodyBar/KFrame.lean`). The sparsity ⟺ arboricity
coincidence above is literally the Nash-Williams condition for the weighted
multigraph `Ĝ` (`P` with multiplicity `6 − ℓ_P`). **(c)** So a route that
needed only (C6) would be *in reach of landed machinery*. The route that is
actually needed is not.

### Step D2 — the menu: matroid intersection, and where even that stops

Fix a colouring and a separator triple. At lengths `ℓ ∈ {1, 3, 5}` — and at
`ℓ = 4` with the (C7) repair of Step D4 — the menu is the **base family of a
partition matroid** on the pairs `(P, L)`:

| `ℓ` | menu | partition parts |
|---|---|---|
| 1 | all five `L ≠ opp(ij)` (forced) | five singletons |
| 3 | `{ij, it, js}`, `s,t ∈ comp` | `{ij}`; `{ik, il}`; `{jk, jl}` |
| 4 (C7) | `{ij, X}`, `X` any other basis line | `{ij}`; the other five |
| 5 | `{ij}` (forced) | one singleton |

Total capacity `Σ_P (6 − ℓ_P) = 6n − 9`, so a maximum common independent set
of that size saturates every part. Hence **(W1) ∧ (W2) at a fixed colouring
and separator triple is exactly a common-base problem for a partition matroid
and the direct sum `⊕_{L∈S} M(G°)/e₀ ⊕ ⊕_{L∉S} M(G°)∖e₀`** — matroid
intersection, decidable in polynomial time with an Edmonds min-max
obstruction certificate. `Matroid.Intersection` (`exists_common_ind`,
`matroid_intersection_minmax`) is live and sorry-free in the
`apnelson1/Matroid` dependency, so this is *expressible* in the project's
setting — but it decides a per-(shape, colouring, triple) question, and the
outer quantifier over colourings is not matroidal.

Where it stops: **length-2 edges.** The (C2)/(C4) options at `ℓ = 2` are
`{ij, ik, jk, kl}` (pt-mode, 4 aligned rows) and `{ij, im, jm}` (meet-plane,
3 aligned + 1 extra) — different sizes, so not a matroid base family at all;
and even restricted to pt-mode the two options differ by a **2-element**
exchange (`{ik, jk}` vs `{il, jl}`), violating the base-exchange axiom. So
the ℓ = 2 dictionary entries genuinely break the matroid structure, and the
`z > 0` extended mode adds a non-linear-algebraic side condition on top
(the extra rows must cut the aligned kernel exactly, checked only by the
exact witness).

### Step D3 — the starvation bound, and the third flank

At a fixed colouring define, for each label `L_pq`, the **menu capacity**
`cap_pq` = the number of `P ∈ E°` that could carry `L_pq` at all:
`{p,q} = colours(P)` (mandatory), or `|{p,q} ∩ colours(P)| = 1` with
`ℓ_P ∈ {1,2,3}`, or `{p,q} = opp(colours(P))` with `ℓ_P ∈ {2,4}`. Since every
class needs `≥ n − 2` members, `cap_pq < n − 2` for any `pq` is an outright
obstruction. Long paths are what starve it: a length-4 edge can carry only
`L_ij` and `L_opp(ij)` (under the pure dictionary), a length-5 edge only
`L_ij`.

**The octahedron flank.** `G° = K_{2,2,2}` with lengths (six 3's, six 4's;
`Σℓ = 42 = 6(12 − 6 + 1)`) is a class shape (`|V| = 36`, `def = 0`,
`hnoRigid`), `χ = 3`, and an admissible colouring **does** exist
(`φ = [0,0,1,1,2,3]`, proper on `G°` and acyclic off `e₀`). Yet over all 8
colourings the pure-dictionary search produces **zero** all-forest
leaves — the failure is (W1) itself, not the separator count, the opposite
pair, or the panel rules. The capacity profile at the witness colouring is
`[2, 5, 7, 7, 7, 7]` against a requirement of `≥ 4`: one class is starved by
2. This is the flank the (C7) repair of Step D4 **rescues** — so it is a
defect of the dictionary, not of the class.

### Step D4 — (C7): the repaired length-4 entry, and what it buys

> **(C7)** *(the named continuation; the length-4 half proven-informally,
> the rest open)* — the (C2) dictionary is **not** exhaustive. At `ℓ = 4`,
> put the free middle `x₂` at a generic point of the face plane `π(i,j,k)`
> and confine *one* end's pencil line to that plane
> (`P_w = Π(w) ∩ π(i,j,k)`), leaving the other generic. All four limit lines
> still span a 4-space (only three lie in the plane), and
> `R_P = ⟨L_ij, L_{x k}⟩` where `x ∈ {i,j}` is the *other* end. Both
> `L_ij` and `L_{xk}` meet every chain line — the two lines through `E_x`
> meet the two chain lines through `E_x` automatically, and both lie in
> `π(i,j,k)` with the remaining two. So the `ℓ = 4` menu is **every**
> 2-subset containing `L_ij` (five options), exactly as free as `ℓ = 3`'s.

12/12 exact witnesses (all colour pairs × both ends). Consequences,
measured: the exhaustive `K4` stratum goes **439 → 702 of 877**; the
octahedron flank of Step D3 becomes solvable; the two structural flanks of
the verdict are **untouched** (they are about the colouring, which the repair
does not move — every repaired option still contains `L_ij`).

Two honest gaps in (C7). **(a)** The rescue is *combinatorial only*: no
full (W1)–(W4) exact witness has been built at a repaired-dictionary member
(the `kslidecl.py` `chain_lines` builder would need the new label wired in,
plus the per-hub compatibility bookkeeping the plane-confined pencil line
implies). **(b)** The analogous question at `ℓ ∈ {1, 2, 5}` is open — and at
`ℓ = 5` the mandatory-`L_ij` claim itself is suspect: with fully generic
middles `L_ij` need not meet `x₂ ∨ x₃`, so `R_P` can be a **non-basis** line,
i.e. an "extra" row in the (C4) sense. That is the one direction that could
also loosen the acyclicity necessity (which assumes every row aligned), at
the price of a larger `z` and a correspondingly weaker structural statement.
It cannot touch the 5-chromatic flank.

### Step D5 — what a class proof now needs

1. **`χ(G°) ≥ 5` shapes** (`K5`, or `Δ(G°) ≥ 5` by Brooks) need a decoration
   with **more than four hub positions** — the tetrahedron's four points are
   the hard cap, and `dim Λ²K⁴ = 6` caps the number of classes at six
   regardless. Whether a 5-or-more-point configuration can still make each
   `R_P` a coordinate subspace is untouched here.
2. **Acyclicity-obstructed shapes** need either a non-aligned (`z > 0`)
   decoration on the offending bicoloured cycles or, again, a bigger
   configuration.
3. **Everything else** is a menu/matroid-intersection question per
   (shape, colouring) — (C6) says the packing side is free, so this half is
   genuinely finite and certificate-bearing, and (C7) is the cheap way to
   enlarge it.
4. **Or drop the collapse.** (C6) is the honest positive residue of this
   pass: the *combinatorial* content of the limit system is uniform and
   landed-machinery-reachable; it is the *alignment* device that fails to be
   class-uniform. A class proof of (K-slide-cl) may be better sought on the
   generic pure condition of the limit system (§(K-slide) Step 3's carrier)
   than on any degenerate specialization of it.

### Verification

`notes/scripts/w4/kslidecomb.py` (tracked; exact ℚ/ℤ arithmetic and asserts
inherited from `repin.py`/`pitch.py`/`kslide.py`/`kslidecl.py`; every sampled
object carries a rank/dimension assert, and every shape is re-certified by
`shape_ok` = tight count + `def = 0` + `hnoRigid`). Reproduce:

| driver | what it asserts |
|---|---|
| `--battery` | control: the 7 §(K-slide) members are class shapes, (C6) holds, and all 7 are menu-solvable (7/7) |
| `--pack` | (C6): min-max slack `≥ 0` over every `F ⊆ E°` **and** an explicit packing with class sizes `{n−2}³ ∪ {n−1}³`, at 7 battery + 2 `K5` shapes |
| `--k5` | properness forced at every `ℓ` (chain-span drop); `χ(K5) = 5`; 5 exhibited `K5` class shapes with 0 collapse assignments but (C6) packings |
| `--acyclic` | `L_ij ∈ A_P` at every length/colour pair; `χ` and acyclic-4-colourability of all 23 hub graphs with `|V°| ≤ 6`; the 4 with `χ ≤ 4` and no acyclic 4-colouring |
| `--flanks` | the three flanks side by side, with the stage-by-stage diagnosis and the starvation profile |
| `--k4full` | exhaustive `K4` stratum: 877 shapes, 877 (C6), 439 menu-solvable, 438 failures **all** with a satisfiable colouring premise |
| `--sweep` | seeded `|V°| ≤ 5` sweep (seed 20260805): 48 shapes, 48 (C6), 18 menu-solvable, 12 colouring-blocked, 18 menu-blocked |
| `--dict4` | (C7): 12/12 exact length-4 witnesses with `R_P = ⟨L_ij, L_xk⟩`, chain span 4 |
| `--relaxed` | the repaired menu: octahedron flank rescued, `K4` stratum 702/877, both structural flanks unchanged |

**Confidence verdict: (K-slide-comb) REFUTED as a class statement** (two
structural flanks at explicit class members; the 5-chromatic one robust
against any tetrahedral decoration, the acyclicity one against any
fully-aligned one); **(C6) — the unrestricted 6-fold base packing — proven-
informally for every class shape** from 5/6-sparsity via Edmonds'
matroid-partition min-max, so the packing content is never the obstruction;
**(C7)'s length-4 repair proven-informally** (12/12 exact witnesses,
`K4` coverage 439 → 702/877, octahedron flank rescued) with its geometric
witness and its `ℓ ∈ {1,2,5}` analogues **open**; and **(K-slide-cl) back to
open**, covered exactly on the shapes where the assignment problem is
solvable (all 7 battery members, hence the `K4`/`W4` control habitats,
unchanged).
