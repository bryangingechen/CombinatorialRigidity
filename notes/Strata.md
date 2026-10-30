# STRATA — body-hinge rank on realization subloci (research note; PENCIL-D's evidence)

**Status:** its `Pᵈ` pencil part opened as **Phase 42** (PENCIL-D, the PI, 2026-10-29; plan
`notes/Phase42-design.md`). Three sessions with the PI after Phase 40: the first found
Results 1–10; the second checked the literature (*Literature*) and ran Results 9–11's tests; the
third set the `Pᵈ` picture, Results 12–19. Phase 42a's tests added Results 20–27. Next concrete
task: Phase 42d's (`notes/Phase42d.md`). No Lean, no blueprint here. Evidence drivers:
`notes/scripts/strata/strata.py` (exact ℚ, seeded) and `oneclass.py` beside it. Editing
discipline as for phase notes (≤ 8-line entries). `HARNESS.md` *Evidence* and *Reproducibility*
bind this work; it is not an attack track.

## The question

The formal proofs give the generic body-hinge rank `6(n−1) − def(G̃)` on three strata of `P³`:
panel (KT), molecular (its polar, Phase 25) and pencil (both at once, Phase 40). Which other
subloci of hinge configurations attain it, in `P³`, in `P⁴` and in every `Pᵈ`, and when one does
not, is its generic rank a clean count? For the pencil the third session's answer is a conjecture
in every `Pᵈ` (Results 12–19), which PENCIL-D sets out to prove.

## Setting and notation

- A **configuration** of a connected multigraph `G` gives each edge `e = uv` a line, with
  Plücker vector `C_e ≠ 0` in `Λ²K⁴ ≅ K⁶`, over an infinite field `K`. The rank is that of the
  body-hinge rigidity matrix (rows `C_e^⊥ ⊗ (e_u − e_v)`). In `P⁴` a hinge is a plane,
  `C_e ∈ Λ³K⁵ ≅ K¹⁰`, so `D = 10`. The rank depends on the hinge vectors only up to one linear
  isomorphism of the screw space, so a configuration may be recorded by its polar dual
  (planes ↔ lines of `P⁴`, containments reversed); the driver says which form each sampler uses.
- In `Pᵈ` a hinge is a `(d−2)`-flat, `C_e ∈ Λ^{d−1}K^{d+1}`, of dimension `D_d = C(d+1, 2)` (3, 6,
  10, 15, 21 at `d = 2, …, 6`). Polarity sends it to a line. From Result 12 on, every `Pᵈ` stratum
  is recorded in this **dual form**: a point `b_v ∈ K^{d+1}` for each hyperplane `B_v`, and the
  hinge `b_u ∧ b_v ∈ Λ²K^{d+1}`.
- `def_D(G) = max_P D(|P|−1) − (D−1)e(P)` is the blueprint's `def:D-deficiency`. **Here the
  subscript is `D`**, not the main-component chapter's `d`: its `def₂` is `def_3` here, its
  `def₃ = def(G̃)` is `def_6`. With `c(P) = e(P) − |P| + 1 ≥ 0`, the cycle rank of the quotient,
  `def_D = max_P (|P|−1) − (D−1)c(P)` is non-increasing in `D`. `def_∞` is its value for
  `D > n + 1`, where only tree quotients count: the number of bridges.
- A **product** stratum lets each hinge range independently over its own family `X_e` of
  lines. A **fibred** stratum is a product once finitely many shared parameters (a common
  point, plane, complex) are fixed. A **coupled** stratum's hinges are determined by per-body
  data (panel, molecular, pencil).
- **Monotonicity**, used throughout: a stratum's generic rank is its maximum rank (over all
  components), and `rank ≥ r` is Zariski-open, so a stratum whose closure contains a
  configuration of rank `r` has one itself. Larger strata never rank lower.

## Results

1. `[PROVED]` **Motion identity.** `rank = D(n−1) − |E| + rank{g_e ⊗ C_e}` (screw dimension
   `D`: 6 in `P³`, 10 in `P⁴`), with `g_e` the column of `e` in a cycle-basis matrix (the
   cographic vectors). A motion modulo the trivial ones is a `λ ∈ K^E` with
   `Σ_{e∈Z} ±λ_e C_e = 0` on every cycle `Z`: Crapo–Whiteley 1982's *motion assignments* (Def
   3.5, Prop 3.3), of which the identity is the dimension count. Checked at 6 sampled strata
   (`--selftest`) and in `P⁴` against a direct rigidity matrix (`--residual4`, `--d4`). It is
   the model of `w4/dominance.py`'s `cycle_data`.
2. `[PROVED]` **Product strata: only the linear spans matter.** If each `X_e` is irreducible
   with linear span `L_e`, the generic rank on `∏X_e` equals that on `∏L_e`. Every minor of
   `[g_e ⊗ C_e]` is multilinear in `(C_e)`; a minor vanishing on `∏X_e` is, with the other
   hinges fixed in their `X_f`, linear in `C_e` and zero on `X_e`, so zero on `L_e`; induct
   over the edges. So the Klein quadric costs nothing on a product stratum. The case `X_e` =
   all lines is Whiteley 1988's specialization to irreducible varieties (Prop 6, Thm 8).
3. `[PROVED]` **The product formula, and its ladder.** On any product stratum the generic
   rank is `6(n−1) − max_{F⊆E} (|F| − dim Σ_{e∈F} g_e ⊗ L_e)`: Results 1–2 and the rank of
   generic points in flats, `min_F |E∖F| + rank(A_F)` (Lovász 1977, as Tanigawa 2012 Thm 2.1
   states it; equivalently Rado 1942, or Lovász 1989 Thm 1* for spaces spanned by rank-one
   matrices). If every `L_e` is one space `L` of dimension `D′`, the sum is
   `span{g_e : e ∈ F} ⊗ L` and the maximum is `def_{D′}`: rank `6(n−1) − def_{D′}(G)`, the
   `D′`-fold union of the cographic matroid; equivalently `L^⊥` is a common row space worth
   `(6−D′)(n−1)`.

   | `D′` | every hinge, independently, … |
   |---|---|
   | 6 | any line (Tay–Whiteley) |
   | 5 | in a fixed linear complex; or meeting a fixed line |
   | 4 | meeting two fixed skew lines |
   | 3 | through a fixed point; in a fixed plane; in one ruling of a fixed quadric (a regulus) |
   | 2 | in a fixed plane through a fixed point of it |

   Check: in a linear complex every cycle of length ≥ 6 loses exactly one degree of freedom
   (`def_5 − def_6`); at `C₆` this is Crapo–Whiteley 1982 Prop 3.4, a ring of six panels is
   infinitesimally rigid iff its hinge lines lie in no linear complex.
4. `[PROVED]` **Fibred strata**, and `[PROVED-MOD Phase 35]` **per-body complexes in `P³`.**
   With shared parameters `θ`, the generic rank is the maximum over `θ` of Result 3's rank
   for the spans `L_e(θ)` (Result 2 fibre by fibre). Per-body special complexes (hinge `uv`
   meets lines `ℓ_u`, `ℓ_v`) and per-body linear complexes (hinge `uv` in complexes `w_u`,
   `w_v`; `L_uv = {w_u, w_v}^⊥`) attain `6(n−1) − def_6`, multigraphs included: with
   `ℓ_v ⊂ Π_v` every hinge-coplanar panel configuration is a special one (two lines of a plane
   meet), special complexes are limits of linear ones, and Phase 35 gives the panel rank.
   Measured as well (`--complexes`, next test 4).
5. `[PROVED-MOD the planar theorem]` **Phase 40's flat rank is the `D′ = 3` rung.** A flat
   pencil configuration has every hinge in one plane `H`; `Λ²H` gives `3(n−1)`, and the rest
   is the planar problem with hinge vectors `p_u ∨ p_v ∈ Λ²H`, polar to Jackson–Jordán's
   pin-collinear frameworks, of rank `3(n−1) − def_3(G)` at a general picture of a simple `G`
   (the planar KT theorem, Phase 40a).
   Total `6(n−1) − def_3(G)`, the value of `6|V| − 3 − dim L(q)` under Jackson–Jordán's
   equality (`sec:main-component-flat`, `sec:main-component-jj`).
6. `[PROVED]` **Coupled strata: the soft argument fails.** (a) The linear span is too coarse:
   "all hinges through one point, the point free" spans all of `(Λ²K⁴)^E` (distinct edges give
   distinct monomials `O_i b_{e,j}`), yet its rank is the `D′ = 3` count at every point: 27,
   not 30, at `C₆`. (b) Intersecting rank-generic strata can lose rank: at `C₆`, three hinges
   meeting a fixed line give rank 30, all six give 29. So the pencil theorem was not a formal
   consequence of the panel and molecular theorems.
7. `[PROVED]` **The four per-body flag conditions of `P³` attain the generic rank** (hinges at
   a body through a point, in a plane, both, or neither): KT, its polar, Phase 40,
   Tay–Whiteley. The meet model identifies parallel hinges, so there this is for simple
   graphs; the containment model (Phase 35) and the pencil theorem cover multigraphs. In `P³`
   two lines meet iff they are coplanar, so these incidences barely cascade. The one cascade
   met, two hubs with three common neighbours (`lem:pencil-x0-two-hubs-obstruction`), cost
   nondegeneracy, not rank. Every per-body stratum containing one of these attains it too.
8. `[PROVED]` incidence fact; rank `MEASURED`, no drop: **a caution in `P⁴`, not borne out.**
   On "the hinges at `v` contain a common line `A_v`" adjacent `A_u`, `A_v` must meet; three
   pairwise-meeting lines are concurrent or coplanar, and coplanar makes a triangle's three
   hinges coincide. The concurrent component (every `A_v` through one point `o`) is the `P³`
   molecular configuration in `K⁵/o`, so its rank is `10(n−1) − def_6` exactly, short of the
   generic `10(n−1) − def_10` wherever `def_6 > def_10` (`C₇`–`C₉`, `C₁₁`, `C₁₂`, `C11ear`). A line-by-line
   construction reaches the generic rank there; the stratum is never short (Result 11).
9. `[MEASURED]` **The `d = 4` pencil's two flat bases.** In `P⁴` the pencil (hinges at `v`
   through `p_v`, inside a hyperplane `B_v`) keeps `p_w ∈ B_v`, `w ∈ N[v]`. `P³`'s flat case
   has two polar `P⁴` analogues. (F2) Every `B_v = H`: hinges in `Λ³H` (`D′ = 4`), a `D = 4`
   residual with each body's hinge vectors in a hyperplane; rank `10(n−1) − def_4` measured
   (`--residual4`, next test 3). (F1) Every hinge through one point: the `P³` molecular
   configuration, `10(n−1) − def_6` by KT (`--d4`, column `pencil0`), the better base since
   `def_6 ≤ def_4`. The `K³` lifting space has no clean count: `dim L(q) − 4 ≥ def_4`,
   unequal at 21 of 38 graphs (`--lifting`).
10. `[CONJECTURED]` **No count formula for arbitrary coupled strata.** Realization spaces of
    incidence configurations can be arbitrarily complicated (Mnëv 1988 Thm A, oriented
    planar types; the algebraic form is Sturmfels 1987, Lee–Vakil 2013) and field-dependent
    (the Fano plane exists only in characteristic 2). No body-hinge stratum whose rank this
    changes has been built.
11. `[MEASURED]` **The six per-body flag strata of `P⁴` attain the generic rank, under cap.**
    Hinges at `v` contain no flat, a point or a line, and lie in a hyperplane or not. A hinge
    containing a line contains a point, so by Monotonicity the minimum (line, hyperplane)
    attaining `10(n−1) − def_10` implies all six. At a seeded point each type reaches it on
    every graph of the `--d4` population, the theorem-backed cells included; the cubic
    diamond rings past the cap (`n = 16, 20`, `--lifting`) reach `10(n−1)`. (line,
    hyperplane) lifts a planar picture by two heights in `L(q)`, `dim L(q) = 3 + def_3`
    measured: Phase 40's lifting space, used twice.
12. `[PROVED]` **The per-body flag poset of `Pᵈ`; the pencil is its bottom.** The hinges at `v`
    contain a `k`-flat `A_v` (`−1 ≤ k ≤ d−3`, `−1` for none), and lie in a hyperplane `B_v` or
    not: `2(d−1)` types (Result 7's four, Result 11's six). Hinges between `A` and `B` span
    `d−1−k` dimensions of the screw space, those through `A` span `C(d−k, 2)`. A **pencil**
    configuration (`k = d−3` with `B`) is a configuration of every type, so by Monotonicity a
    pencil theorem implies all `2(d−1)`. Katoh–Tanigawa's all-`d` theorem is the type `(−1, B)`.
    Polarity sends `(d−2)`-flats to lines, so it identifies "through a point" with KT only at
    `d = 3`. At `d = 2` panel and pencil coincide (pins collinear per body, Jackson–Jordán 2008).
13. `[PROVED]` **The pencil of `Pᵈ` in dual form, and its parameters.** A panel configuration
    (hinge `uv` = `B_u ∩ B_v`, dual `b_u ∧ b_v`) is a pencil iff the panels of each closed
    neighbourhood share a `(d−3)`-flat, iff each `b_{N[v]}` lies in a plane: the same condition
    in every `d`. If the projection to `P²` from a generic `(d−3)`-flat is an admissible picture
    `q`, each such plane is the graph of an affine map, so every coordinate lies in Phase 40's
    `L(q)`: `b_v = (q_v, z¹_v, …, z^{d−2}_v, 1)` with `zⁱ ∈ L(q)`. So `d = 2` has no heights,
    `d = 3` one (Phase 40) and `d = 4` two (Result 11). With `z^{d−2} = 0` it is the `P^{d−1}`
    pencil in a hyperplane, of rank `D_d(n−1) − def_{D_{d−1}}` where that theorem holds.
14. `[PROVED]`, the pattern `[CONJECTURED]`: **codimension does not decide; what is shared
    does.** At `C₆` in `P³` (configurations: dimension 24) the panel stratum (dimension 18)
    attains 30 and "all six meet one line" (dimension 22) has 29 (Result 6(b)). The drop locus
    is the hypersurface `det[C₁ … C₆] = 0` (Result 1, one cycle), so attaining is a
    non-containment, blind to dimension. For an isostatic bar-and-body framework the drop
    locus is one polynomial, White–Whiteley 1987's *pure condition*. In `Pᵈ` the panel stratum
    has codimension `2(d−1)|E| − dn`, unbounded, and attains. The pattern in every case met: a
    shared span `D′` costs `def_{D′}` (Result 3); the same span chosen per body costs nothing.

    | hinges at each body … | shared by all bodies | chosen per body |
    |---|---|---|
    | in a hyperplane (span `d`) | `def_d` (Result 3; rigidity half: Jackson–Jordán 2010 Thm 6.5) | `def_D` (KT, every `d`) |
    | through a point (span `C(d,2)`) | `def_{C(d,2)}` (Result 3) | `def_D` at `d = 3` (KT's polar); `d = 4` measured (Result 11) |
    | a pencil (span 2) | `def_2` (Result 3) | `def_D` at `d ≤ 3` (KT, Phase 40); `d = 4, 5, 6` measured (Results 11, 19) |

    Result 8 fits: its cascade forces a shared point only across triangles sharing edges. Their
    union has a spanning 2-tree, rigid at every `D ≥ 3`, so the sharing is forced where it is free.
15. `[PROVED]` **Embedding: a pencil witness in `P^{d′}` is one in every `Pᵈ`, `d ≥ d′`.** An
    injective linear map `K^{d′+1} → K^{d+1}` keeps every closed neighbourhood coplanar and
    keeps Result 1's cycle term `rank{g_e ⊗ C_e}`, since `Λ²` of it is injective. So a `P^{d′}`
    configuration of rank `D_{d′}(n−1) − def_{D_{d′}}` maps to one of rank
    `D_d(n−1) − def_{D_{d′}}`, the `Pᵈ` target iff `def_{D_{d′}} = def_{D_d}`. By Result 16 this
    holds when `def_3(G) + 3 ≤ D_{d′}`. So for each `G` only `3 ≤ d ≤ d*` needs a proof, where `d*`
    is the least `d′` with `D_{d′} ≥ def_3(G) + 3`, and the case `d*` implies every `d` above it
    (the old threshold `2 + def_3` was the special case of Result 16's old form). Jackson–Jordán's
    equality is not used. Formalized in Phase 42c as `hasGradedPencilRealization_of_le` (the
    realization) and `Graph.X0AttainsGrade.of_le` (the configuration), over
    `BodyHingeFramework.finrank_span_rigidityRows_map_injective`.
16. `[PROVED]` **The deficiency lemma (sharp form).** For a **connected** `G` with `t = def_3(G)`,
    `def_{D′}(G) = def_D(G)` whenever `t + 3 ≤ D′ ≤ D`. A partition `P` whose quotient has cycle
    rank `c ≥ 1` has value at `D` at most `t − (D − 3)c ≤ t − (D′ − 3) ≤ 0`, so it never beats
    the trivial partition; a tree quotient has value `|P| − 1` at every `D`. It is tight on cycles
    (`C₇`: `def_3 = 4`, `def_6 = 1`, `def_10 = 0`), and connectivity is needed (two bodies and no
    edge have `def_D = D`). In particular, with `ℓ = 3 + t`, `def_{C(ℓ,2)}(G) = def_∞(G)`, so
    `def_D = def_∞` for every `D ≥ C(ℓ,2)`: the old form, whose proof bounded `t ≥ |P| − 1 − 2c >
    (D′−3)c ≥ C(t+3, 2) − 3 = (t² + 5t)/2`, impossible for `t ≥ 0`. `--pd` asserted the old form on
    all 38 graphs of the `--d4` population, multigraphs included (a record of what it asserted).
    Formalized in Phase 42c as `Graph.Connected.deficiency_eq_of_deficiency_two_add_three_le`.
17. `[PROVED-MOD Phase 40]` **Corollary: the `Pᵈ` pencil theorem for every `d` when
    `def_3(G) ≤ 3`.** For `G` under the main component's standing hypotheses
    (`def:pencil-x0-standing`): at `def_3 = 0` embed the planar theorem's witness (`d′ = 2`,
    Phase 40a); at `1 ≤ def_3 ≤ 3` embed Phase 40's (`d′ = 3`, `D′ = 6 ≥ def_3 + 3`; the first widening of the old `def_3 ≤ 1`, by the sharp Result 16). Then Results 15–16 apply. The content range at `d` (graphs not settled from `P^{d−1}`) is `def_3 ≥ C(d,2) − 2` (`≥ 4` at `d = 4`, `≥ 8` at `d = 5`), and a `P⁴` theorem gives every `d` at `def_3 ≤ 7`. This is the
    first `Pᵈ` statement in reach of the existing formal proofs (PD-STABLE). Formalized in Phase
    42c, at `d′ = 3` throughout, as `Graph.x0AttainsGrade_of_deficiency_two_le_three` and
    `Graph.hasGradedDistinctPencilRealization_of_deficiency_two_le_three`.
18. `[PROVED-MOD Jackson–Jordán's equality]` **The universal configuration: stabilization in
    `d`.** Every coordinate of a configuration of Result 13 lies in `L(q)`, of dimension
    `ℓ = 3 + def_3` at a general picture (`thm:pencil-jj-equality`). So every such `Pᵈ`
    configuration over `q` is a linear image of one `β_q : V → K^ℓ` (a basis of `L(q)`,
    evaluated), injective for `d ≥ ℓ − 1`. Its points span at most `ℓ` dimensions, a forced shared
    span that Result 16 makes free. For `d ≥ 2 + def_3` all the `Pᵈ` statements are the one
    statement about `β_q`, the converse of Result 15. In KT's dual form the points are free, a
    linear image of the simplex on `V`, so there only `d ≤ n − 2` has content.
19. `[MEASURED]` **The pencil of `Pᵈ` at `d = 4, 5, 6`.** `--pd`, seeds 1–3: on the 36 simple
    graphs of the `--d4` population, `n ≤ 12`, each point reaches `D(n−1) − def_D` at every
    `d = 2..6`. This is asserted at `d = 2, 3`, and reported at `d ≥ 4` with no cell below.
    Past the cap, 8 graphs with `n ≤ 25` (theta graphs, subdivisions, diamond rings) reach
    `D(n−1)` at all 24 cells, which certifies. Most capped graphs have `def_3 ≤ 2`, so they are in
    the stable range from `d = 4` (Result 18). The cells outside it at `d ≥ 4` are 26, on 11
    sparse capped graphs, and 15 past the cap. Not found below target, under that cap.
20. `[MEASURED]` **Row 5's flat formulas in `Pᵈ`** (Phase 42a's T1; `--content`, seeds 1–3). The
    flat configuration (every height zero) has rank `D(n−1) + 3 − dim L(q)` at all 38 graphs of the
    `--d4` population, `d = 4, 5, 6`. R1's base (the last height zero: the `P^{d−1}` pencil in a
    hyperplane) has `10(n−1) − def_6` at `d = 4` on the 36 simple graphs, and
    `D(n−1) − def_{D_{d−1}}` at `d = 5, 6`. It is at the `Pᵈ` target on 30, 34 and 36 of them. The six
    it misses at `d = 4` are `C₇`–`C₉`, `C₁₁`, `C₁₂` and `C11ear`. The flat configuration is at the
    target on 22, the graphs with `def_3 = 0`.
21. `[MEASURED]`, the `D`-gon `[PROVED]` at even `d`: **CERT's certificates** (Phase 42a's T2;
    `--content`, seed-independent). At `d = 3..6` each one rows 10–12 use exists, its joins
    independent over every field (Smith invariant factors 1). By search in `{−1, 0, 1}`: closed
    `m`-gons, `m < D`; open ears `a, x₁, …, x_k, b`, `k ≤ D − 2`, at height zero at `a, x₁, x_k, b`.
    The `D`-gon of the cycle and the long ear is built on a unimodular basis `P₀, …, P_d`, three
    consecutive points at height zero: at even `d` an Euler circuit of `K_{d+1}`, whose joins are the
    basis `P_i ∧ P_j`; at odd `d` one of `K_{d+1}` minus a perfect matching, with a detour through
    `P_j + P_k − P_i` per matching edge `ij` (checked at `d = 3, 5`).
22. `[MEASURED]` **The content range where the `P³` proof breaks** (Phase 42a; `--content`, seeds
    1–3). All 38 cells with `4 ≤ d ≤ 2 + def_3`, on 15 graphs (drawn on the old, wider range `def_3 ≥ d − 2`, a superset of the content range of Result 17 at every `d ≥ 3`), reach their target. `θ(2, 2, k)` for
    `k = 4..10` has row 14's one-body ear with ends sharing a neighbour (`def_3 = k − 2` under the
    cap). `θ(2, 2, 2, k)` for `k = 5..10` has two hubs with three common neighbours
    (`def_3 = k − 3`). The diamond rings at `m = 6, 7` (`n = 24, 28`) carry a condition at every
    body, up to `d = 6`. Targets as in Result 19: 24 cells under the cap, 14 certified past it. With
    §2.5's 47 cells (`notes/Phase42-design.md`), 85, none below. D's witness has `def_3 = 0`.
23. `[MEASURED]`, one bound `[PROVED]`: **The one-body ear on its incidence locus** (Phase 42a's
    T4, first half; `--oneear`, seeds 1–3). For an ear `a − x − b` at non-adjacent ends, `G`'s
    configurations restrict to the locus `b_x ∈ Π_a ∩ Π_b`, where `lem:pencil-one-ear-incidence`
    needs `G₁ = G − x` at its target. There `G₁` reaches it at all 26 cells, `d = 4, 5`, of
    `θ(2, 2, k)` (`k = 4..10`; the ends share a neighbour) and `θ(2, 3, k)` (`k = 4..9`; none), and
    at 11 of 12 on `θ(2, 2, 2, k)` (`k = 5..10`; two, and the step's merged hypothesis fails). The
    miss, `k = 10` at `d = 4`, is forced: the hubs' planes coincide, so the cycle `a y b w` has
    dependent hinges, and the `k`-path extends that to a motion of `G₁` once its hinges span `Λ²`
    (`k ≥ D`). The proof and the cells: `notes/Phase42-design.md` §2.4.
24. `[MEASURED]`, one implication `[PROVED]`: **The short ears' obstruction does not occur** (Phase
    42a's T3; `--short`, seeds 1–3). On 198 danger cells at `d = 4, 5` (an open ear, `3 ≤ k ≤ D − 2`,
    `def_D(G[V₁]) > def_D(G) = def_D(G'')`, `2d − 1 ≤ dim W ≤ D − 1`; six families, `n ≤ 40`) the
    span `W` of the step at `G''` contains neither star unless `W = Λ²`, and `x₂` put back gains the
    dimension `(⋆)` needs. Modulo `star(y₁) + star(y₃)`, of codimension `C(d−1, 2)`, `W`'s image is
    always everything: the joins `y₄ y₅, …, y_k p_b` fill it once `k ≥ C(d−1, 2) + 3`, which a
    certificate proves for every graph, and below that `ρ`'s image supplies the rest, in general
    position. The 24 cells at `d = 3`, where the chapter proves the step, are the control. The
    argument and the cells: `notes/Phase42-design.md` §2.3–2.4.
25. `[MEASURED]` **The orbit ears follow the merged hypothesis** (Phase 42a's T4, second half;
    `--orbit`, seeds 1–3). Open ears with one or two interior bodies at non-adjacent ends where
    `def_D(G[V₁]) > def_D(G)`, so row 12 does not apply; content range, `d = 3..6`, `n ≤ 40`. At all
    46 one-body cells `G[V₁]` attains on the incidence locus and `(⋆)` holds, with
    `dim(ρ + Λ) = min(dim ρ + 2, D)`. At all 69 two-body cells Phase 40's route reaches
    `min(s + 1, dim(ρ + Λ²(A+B)))`; that is `(⋆)` at all 62 where the merged hypothesis holds.
    Where it fails (7 cells, `d = 3` included) the locus forces `Π_a = Π_b`, the route falls one
    short, and `G` still attains. The cells: `notes/Phase42-design.md` §2.4.
26. `[PROVED]`, two reductions, the rest `[MEASURED]`: **The coverage at `D`** (Phase 42a's T5;
    `--coverage`, seed-independent). Theorem S, the coverage's last case, holds at every `D ≥ 6`,
    so no step uses a one-body ear with `def_D(G[V₁]) > def_D(G)`. At `D ≥ 10`, a graph past the
    first five rows with no step free of new mathematics has a chain of 3+ interior bodies, or
    `def_D(G) = 0` and only one-body chains. On subdivisions of ten cores (paths of 1–4 edges:
    1059, 1021, 957 cells at `d = 4, 5, 6`; 542 more with paths of 1–2) every cell has such a step,
    a core at all but three. Petersen with every edge a 4-path (`d = 4`) or a 6-path (`d = 5`) has
    only SHORT-CORE's rows. The arguments and cells: `notes/Phase42-design.md` §2.4.
27. `[PROVED]`, checked `[MEASURED]`: **ONE-CLASS is Phase 40's** (Phase 42a; `oneclass.py`).
    Let `G` be sparse, of minimum degree two, with no two bodies of degree two adjacent, and let
    `D ≥ 6`. If `def_6(G) > 0`, a set of least `s_3` among those of `def_D` zero is a core at `D`.
    So a graph whose chains are all one-body has a core at `D`, or `def_6(G) = 0 = def_D(G)`, and
    then Phase 40's `P³` witness embeds (Result 15). ONE-CLASS needs no ONE-EAR, and with Result
    26 the coverage at `D ≥ 10` needs no new mathematics beyond SHORT-CORE. Checked exactly at
    `D = 6, 10, 15, 21`: the proof's set is a core at all 151 necklace cells with `def_6 > 0`. On
    14 017 cells over T5's and nauty's cores `def_6 > 0` never occurs, and the 523 with no core
    have `def_3 ≤ 2`. The proof: `notes/Phase42-design.md` §2.3.

## The PENCIL-D program

Opened 2026-10-29 with the PI as **Phase 42**: the target, the routes, the layers and the PI's
decisions are `notes/Phase42-design.md`, the recon's work log `notes/Phase42a.md` (closed 2026-10-30).
SHORT-CORE, the coverage's new mathematics after Results 26–27, is settled by its attack track:
`notes/attacks/short-core/state.md`, results by workbook S-number.

## Literature (next test 1, 2026-10-29)

Read in `.refs/` or checked against Crossref; page numbers are printed pages.
- **Result 1:** Crapo–Whiteley 1982, Def 3.5 and Prop 3.3 (p. 66). The rank identity itself
  is not stated in the sources read.
- **Result 2:** only for `X_e` = all lines: Whiteley 1988 Prop 6 and Thm 8 (p. 243);
  Tanigawa 2012, proof of Thm 3.1.
- **Result 3:** not found as stated. Its ingredients are Whiteley 1988 Thm 1 (a `k`-frame is
  a union of `k` forests, p. 239), Jackson–Jordán 2010 Thm 6.5 (all hinges in one
  hyperplane, rigid when `(d−1)G` has `d` disjoint spanning trees: the rigidity half of the
  plane rung, p. 583) and Crapo–Whiteley 1982's catalogue of linear line families (p. 56).
- **Result 4:** nearest are Tay 1989 and Tanigawa 2012's rod-bar frameworks, whose bars meet
  two per-body lines; they treat bars, not hinges, with a Dilworth-truncation count.
- **`C₆` in a linear complex:** Crapo–Whiteley 1982 Prop 3.4 (p. 67; its "k ≥ 6" is a misprint
  for `k > 6`, per its proof).
- **Result 14:** White–Whiteley 1987, from its Crossref abstract only (the publisher page refused
  the fetch): for an isostatic bar-and-body multigraph, one polynomial, the *pure condition*,
  gives the positions where infinitesimal rigidity fails. Its body-hinge form is not checked.
- **Results 12–19:** nothing searched yet beyond the sources above.
- **Searched, nothing found:** the in-tree rigidity PDFs (`REFS.md`) for linear complexes,
  special positions, `k`-frames and hinges meeting a line. Not read: Hunt 1967, Lovász 1977.

Citations: Crapo, Whiteley, *Structural Topology* 6 (1982) 43–82 (`crapoWhiteley1982`);
Whiteley, *SIAM J. Discrete Math.* 1 (1988) 237–255, doi:10.1137/0401025; Jackson, Jordán,
*European J. Combin.* 31 (2010) 574–588, doi:10.1016/j.ejc.2009.03.030; Jackson, Jordán,
*Discrete Comput. Geom.* 40(2) (2008) 258–278, doi:10.1007/s00454-008-9100-z
(`jacksonJordan2008pin`); White, Whiteley, *SIAM J. Algebraic Discrete Methods* 8(1) (1987)
1–32, doi:10.1137/0608001; Tanigawa, *SIAM J. Discrete Math.* 26 (2012) 1412–1439,
doi:10.1137/100819473; Lovász, "Flats in matroids and
geometric graphs", Proc. 6th British Combin. Conf., Academic Press (1977) 45–86; Lovász,
*Bol. Soc. Bras. Mat.* 20 (1989) 87–99, doi:10.1007/BF02585470; Rado, *Quart. J. Math.
Oxford* 13 (1942) 83–89, doi:10.1093/qmath/os-13.1.83; Mnëv, LNM 1346 (1988) 527–543,
doi:10.1007/BFb0082792; Sturmfels, *Bull. AMS* 17 (1987) 121–124,
doi:10.1090/S0273-0979-1987-15532-7; Lee, Vakil, Clay Math. Proc. 18 (2013) 457–468,
arXiv:1202.3934; Katoh, Tanigawa, *Discrete Comput. Geom.* 45 (2011) 647–700 (all `d ≥ 2`);
Hunt, *J. Mechanisms* 2 (1967) 307–327, doi:10.1016/0022-2569(67)90005-5.

## Evidence

Eight commands, `N ∈ {1, 2, 3}`, verdict `OK: every target met` at all three:
`python3 notes/scripts/strata/strata.py --linear --mixed --perbody --examples --selftest
--seed N` and `... --complexes --residual4 --d4 --lifting --seed N` (~20 s each), `... --pd
--seed N` and `... --content --seed N` (~4 s each), `... --oneear --seed N` (~1 s) and
`... --short --seed N` (~70 s), `... --orbit --seed N` (~60 s) and `... --coverage --seed N`
(~110 s). Output is byte-identical
under `PYTHONHASHSEED` 0 and 7.
- **First command** (session 1; byte-identical after sessions 2 and 3): 184 linear cells
  (23 graphs × 8 rungs) where the rank at a point, the count and the rank at the per-edge
  linear envelope agree; 7 mixed cases; every per-body cell (molecular, panel, pencil, flat
  pencil) at its count; both `C₆` sentences of Result 6 asserted; the self-test rejects a
  constructed witness for each of 10 guards, and the deficiency oracles agree (131 checks).
- **`--complexes`, `--residual4`:** the 23 graphs, every cell at its count; Result 3's
  min-max, brute-forced over `F` at `|E| ≤ 9`, agrees with the envelope rank (24 checks).
- **`--d4`:** 38 graphs, `n ≤ 12`, 36 simple: the 23, 7 triangle-rich ones, the cube,
  Petersen, and 6 sparse ones, of which `C₁₁`, `C₁₂`, `C5-C5` have `def_10 > 0`; coupled
  types on simple graphs only. The line-by-line sampler degenerates at `K3,3` only, where the
  concurrent one reaches the count. **`--lifting`:** the planar identity at all 36 simple
  graphs; the diamond rings at `m = 3, 4, 5`.
- **`--pd`** (session 3; the nine earlier modes' output byte-identical, compared at seed 1
  against the previous driver): Result 19's cells; Result 16 on all 38 graphs; at each simple
  graph `dim L(q) = 3 + def_3`, the points spanning `min(d+1, dim L(q))`, and `def_D = def_∞`
  through the stable range. Support: one picture per graph, fresh heights per `d`.
- **`--content`** (Phase 42a; the ten earlier modes' output byte-identical at seeds 1–3 against
  the previous driver): Results 20–22. Asserted: Result 20's flat rank at every cell and its
  `d = 4` base at every simple graph, Result 21's certificates (with the chapter's hexagon and a
  determinant-2 negative control), and under the cap `dim L(q) = 3 + def_3` and the design's
  bounds on `def_3`. Support as `--pd`: one picture per graph, fresh heights per `d`; the flat
  configuration varies the picture only. T2 searches the box `{−1, 0, 1}`, seeded by `(d, m)`
  alone, so its lines are seed-independent. In-code fences: the families of Result 22 stop at
  `k = 10` and `m = 7`, T2 at `d = 6`.
- **`--oneear`** (Phase 42a's T4; the eleven earlier modes' output byte-identical at seeds 1–3
  against the previous driver): Result 23. Asserted: each ear's shape (`x` adjacent to the hubs
  only, the hubs not adjacent), `dim Π_a = dim Π_b = 3` and `b_x ∈ Π_a ∩ Π_b` at `G`'s
  configuration, every rank at most its count, `dim L(q) = 3 + def_3` for `G` and `G₁` under the
  cap, and on `θ(2, 2, 2, k)` the forced motion's premises with its bound. Reported: the ranks,
  `dim(Π_a ∩ Π_b)` and the `d = 3` step's two hypotheses. Support: one picture per graph, fresh
  heights per `d` for `G` and for `G₁`'s control at the same picture. Fences: `d ∈ {4, 5}`,
  `k ≤ 10` (`k ≤ 9` for `θ(2, 3, k)`), the DP cap at `n₁ ≤ 12`. The cells do not vary with the seed.
- **`--short`** (Phase 42a's T3; the twelve earlier modes' output byte-identical at seeds 1–3
  against the previous driver): Result 24. Asserted at every cell: each deficiency, a partition's
  value matched by a generic-hinge rank (`def_certified`; `n ≥ 17` at `d = 4, 5`); the ear rank
  formula at `G''` and at `G`; every rank at most its count; `dim W = k + f − def_D(G'')` where
  `G[V₁]` and `G''` attain; a positive control of the containment test. At `d = 3` also `G[V₁]`
  and `G''` at target, X3 and the step's `(⋆)`. Support: one picture and heights of `G''` per
  cell, then fresh ear data; a failed guard redraws the point (`~`, once at seed 2). Population:
  `SHORT_PER = 2` danger cells per family, `d` and `k`, by a box search seeded by them alone
  (`SHORT_TRIES = 400`, `n ≤ 40`), so the cells and their figures do not vary with the seed; the
  four-path theta has none at `d = 5`, `k ≥ 11`, under that cap.
- **`--orbit`** (Phase 42a's T4, second half; the thirteen earlier modes' output byte-identical at
  seeds 1–3 against the previous driver): Result 25. Asserted at every cell: each deficiency
  certified (`def_certified`), the ear rank formula at every configuration, every rank at most
  its count, `dim W = 2 + f − def_D(G₁)` where `G[V₁]` and `G₁` attain, and each end off the
  other's plane wherever the merged hypothesis holds (certified per cell as
  `def_3(G[V₁]) − def_3(G[V₁] + ab) = 2`). At `d = 3` where the ends are off,
  `lem:pencil-insertion-two`'s bound. Support: per cell one configuration of `G` (`k = 1`), or
  of `G₁` then a general insertion, and one of `G` (`k = 2`). Population: `--short`'s families,
  `ORBIT_PER = 2` cells per family, `d`, `k` and class (`danger` where `dim W` can hold
  `Λ²(A+B)`, its meet measured at a configuration seeded with the cell), by a box search seeded
  by them alone (`ORBIT_TRIES = 400`, `n ≤ 40`), plus Result 23's two `d = 4` cells; the rows do
  not vary with the seed, and no point was redrawn. The four-path theta has none at `d = 6`.
- **`--coverage`** (Phase 42a's T5; the fourteen earlier modes' output byte-identical at seeds 1–3
  against the previous driver): Result 26. No point is drawn: every figure is exact combinatorics
  on a subdivision of a core, by `core_def` (exact by its docstring's argument; checked against
  the `3^n` DP in 23 717 checks at `n ≤ 12`, where each core found is re-verified on the
  bodies). Asserted at every cell: the coverage at `D`, the chain facts of Theorem S's proof read
  at `D` (1 578 one-body chains with `x₁` in a set of `def_D` zero), the `D ≥ 10` reduction,
  C's hand count, and the Petersen cells' predicted class. Population: `COV_CORES`, ten cores of
  minimum degree 3, paths of `1..COV_LMAX = 4` edges; every vector up to isomorphism where
  `4^E ≤ COV_EXHAUST = 4096` (five cores), else `COV_PER = 60` of `COV_TRIES = 3000` draws seeded
  by core, `d` and box; simple, sparse, in the content range; then a box of paths of 1–2 edges.
  Fences: `d ≤ 6`, paths of at most 4 edges, cores of at most 10 bodies (`core_def` is `3^nc`).
- **`oneclass.py`** (Phase 42a, ONE-CLASS; a new driver beside `strata.py`, importing it, so
  no earlier figure can move): Result 27, by `python3 notes/scripts/strata/oneclass.py --cores
  --necklaces` (~20 s) and `(for n in 4 5 6 7 8; do geng -C -d3 -q $n 0:12; done) | python3
  notes/scripts/strata/oneclass.py --g6 -` (~50 s; nauty's `geng`, external). Asserted per cell
  and `D ∈ {6, 10, 15, 21}`: a set of least `s_3` among those of `def_D` zero (a proper one on a
  tie) is proper where `def_6 > 0`, is proper exactly where `cov_core` finds a core, and is
  then a core, re-checked on the bodies by the `3^n` DP at `n ≤ 9`. Population: T5's ten
  cores, then all 45 cores (2-connected, minimum degree 3) on 4–8 bodies with at most 12 edges,
  every length vector in `{1, 2}^E` up to automorphism (Petersen: 60 of 3000 draws); 279 and
  13 738 cells, `def_6 = 0` at every one. Then three necklaces (four or five diamonds, or a
  `K₄ − e` and three diamonds, in a ring), every length: 432 cells, 151 with `def_6 > 0`.
  `--cores --necklaces` is byte-identical under `PYTHONHASHSEED` 0 and 7. Fences: cores of at
  most 10 bodies, no core path longer than 2 (the lemma's own hypothesis).
- **Bounds:** a point's rank is a lower bound for the stratum's generic rank, and each count
  an upper bound (Results 3, 5, and `D(n−1) − def_D` in `Pᵈ`), so a match certifies the
  generic rank on that graph. A shortfall at a point would prove nothing.
- **Caps:** the 38 labelled graphs are a cap, not a census (the `3^n` deficiency DP stops at
  `n ≤ 12`); `--pd`'s 8 past-cap graphs are certified only by reaching `D(n−1)`. Section
  draws are once per rung per run in `--linear`; per-body data is drawn afresh per graph. Fixed
  constants `COORD = 1000`, `SPAN_SAMPLES = 12`, `LOVASZ_MAX_EDGES = 9`, `CERT_TRIES = 1000`.

## Next tests

1. **PD-RECON's step table**, landed as Phase 42a's (`notes/Phase42-design.md` §2.1). It
   absorbed session 2's test "a proof for (line, hyperplane) in `P⁴`": R1 at `d = 4`.
2. **Past the cap:** a `D`-general deficiency oracle (Result 3: `def_{D′}` is a matroid-union
   rank, so polynomial) would turn `--pd`'s past-cap rows into full tests at every `d`. The
   harness's polynomial oracles are `D = 6` only. The cells that matter are those outside the
   stable range (Result 19), so sparse graphs with large `def_3`.
3. **Literature left:** Hunt 1967 (screw axes, 6R mobility, the linear complex); Lovász 1977
   (not in `.refs/`; cited here through Tanigawa and Lovász 1989); White–Whiteley 1987 itself
   (whether the pure condition has a body-hinge form); a search for Results 12–19.
4. **Beyond the flag poset** (not PENCIL-D's): per-body conditions whose closure avoids every
   pencil configuration, such as per-body reguli in `P³`, if their incidence variety does not
   degenerate to pencils. Also conditions coupling hinges around cycles rather than at bodies,
   which Result 14's pattern predicts lose rank (Crapo–Whiteley's ring of six panels).
5. Results 1–3 look formalizable as a small phase on the matroid-union layer (Phases 12–14)
   and `def:D-deficiency`, apart from PENCIL-D. Queuing it is the PI's call.
