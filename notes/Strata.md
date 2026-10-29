# STRATA — body-hinge rank on realization subloci (research note)

**Status:** unqueued (2026-10-29). Two sessions with the PI after the pencil realization
theorem (Phase 40): the first found Results 1–10, the second checked the literature
(*Literature*) and ran next tests 2–4 (Results revised in place, Result 11 new). No phase,
no Lean, no blueprint. Evidence driver: `notes/scripts/strata/strata.py` (exact ℚ, seeded).
Further tests are for a fresh session (*Next tests*). Editing discipline as for phase notes
(≤ 8-line entries). `HARNESS.md` *Evidence* and *Reproducibility* bind this work; it is not
an attack track.

## The question

The formal proofs give the generic body-hinge rank `6(n−1) − def(G̃)` on three strata of `P³`:
panel (KT), molecular (its polar, Phase 25) and pencil (both at once, Phase 40). Which other
subloci of hinge configurations attain it, in `P³` and in `P⁴`, and when one does not, is its
generic rank a clean count?

## Setting and notation

- A **configuration** of a connected multigraph `G` gives each edge `e = uv` a line, with
  Plücker vector `C_e ≠ 0` in `Λ²K⁴ ≅ K⁶`, over an infinite field `K`. The rank is that of the
  body-hinge rigidity matrix (rows `C_e^⊥ ⊗ (e_u − e_v)`). In `P⁴` a hinge is a plane,
  `C_e ∈ Λ³K⁵ ≅ K¹⁰`, so `D = 10`. The rank depends on the hinge vectors only up to one linear
  isomorphism of the screw space, so a configuration may be recorded by its polar dual
  (planes ↔ lines of `P⁴`, containments reversed); the driver says which form each sampler uses.
- `def_D(G) = max_P D(|P|−1) − (D−1)e(P)` is the blueprint's `def:D-deficiency`. **Here the
  subscript is `D`**, not the main-component chapter's `d`: its `def₂` is `def_3` here, its
  `def₃ = def(G̃)` is `def_6`.
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
- **Searched, nothing found:** the in-tree rigidity PDFs (`REFS.md`) for linear complexes,
  special positions, `k`-frames and hinges meeting a line. Not read: Hunt 1967, Lovász 1977.

Citations: Crapo, Whiteley, *Structural Topology* 6 (1982) 43–82 (`crapoWhiteley1982`);
Whiteley, *SIAM J. Discrete Math.* 1 (1988) 237–255, doi:10.1137/0401025; Jackson, Jordán,
*European J. Combin.* 31 (2010) 574–588, doi:10.1016/j.ejc.2009.03.030; Tanigawa, *SIAM J.
Discrete Math.* 26 (2012) 1412–1439, doi:10.1137/100819473; Lovász, "Flats in matroids and
geometric graphs", Proc. 6th British Combin. Conf., Academic Press (1977) 45–86; Lovász,
*Bol. Soc. Bras. Mat.* 20 (1989) 87–99, doi:10.1007/BF02585470; Rado, *Quart. J. Math.
Oxford* 13 (1942) 83–89, doi:10.1093/qmath/os-13.1.83; Mnëv, LNM 1346 (1988) 527–543,
doi:10.1007/BFb0082792; Sturmfels, *Bull. AMS* 17 (1987) 121–124,
doi:10.1090/S0273-0979-1987-15532-7; Lee, Vakil, Clay Math. Proc. 18 (2013) 457–468,
arXiv:1202.3934; Katoh, Tanigawa, *Discrete Comput. Geom.* 45 (2011) 647–700 (all `d ≥ 2`);
Hunt, *J. Mechanisms* 2 (1967) 307–327, doi:10.1016/0022-2569(67)90005-5.

## Evidence

Two commands, `N ∈ {1, 2, 3}`, ~20 s each, verdict `OK: every target met` at all three:
`python3 notes/scripts/strata/strata.py --linear --mixed --perbody --examples --selftest
--seed N` and `... --complexes --residual4 --d4 --lifting --seed N`. Output is byte-identical
under `PYTHONHASHSEED` 0 and 7.
- **First command** (session 1; byte-identical after session 2's edits): 184 linear cells
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
- **Bounds:** a point's rank is a lower bound for the stratum's generic rank, and each count
  an upper bound (Results 3, 5, and `10(n−1) − def_10` in `P⁴`), so a match certifies the
  generic rank on that graph. A shortfall at a point would prove nothing.
- **Caps:** the 38 labelled graphs are a cap, not a census (the `3^n` deficiency DP stops at
  `n ≤ 12`). Section draws are once per rung per run in `--linear`; per-body data is drawn
  afresh per graph. Fixed constants `COORD = 1000`, `SPAN_SAMPLES = 12`,
  `LOVASZ_MAX_EDGES = 9`.

## Next tests (a fresh session)

1. **A proof for (line, hyperplane) in `P⁴`** (Result 11's minimum, hence all six): the
   planar picture lifted by two heights in `L(q)`. Phase 40 lifts by one height from the
   `def_3` flat base to `def_6`; here two heights must reach `def_10`. First assess whether
   Phase 40's argument (`sec:main-component-flat`) runs per height.
2. **The `P⁴` pencil from base (F1)** (Result 9): lift from `10(n−1) − def_6` (a theorem) to
   `def_10`. It is implied by next test 1, but its lifting space is the `K³` one, which has no
   clean count.
3. **Past the cap:** a `D`-general deficiency oracle (Result 3: `def_{D′}` is a matroid-union
   rank, so polynomial) would take the census beyond `n = 12`. The harness's polynomial
   oracles are `D = 6` only.
4. **Literature left:** Hunt 1967 (screw axes, 6R mobility, the linear complex); Lovász 1977
   (not in `.refs/`; cited here through Tanigawa and Lovász 1989).
5. If the picture survives: Results 1–3 look formalizable as a small phase on the
   matroid-union layer (Phases 12–14) and `def:D-deficiency`. Queuing it is the PI's call.
