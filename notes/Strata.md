# STRATA — body-hinge rank on realization subloci (research note)

**Status:** unqueued (2026-10-29). One exploratory session with the PI, after the pencil
realization theorem (Phase 40); further tests are for a fresh session (*Next tests*). No phase,
no Lean, no blueprint. Evidence driver: `notes/scripts/strata/strata.py` (exact ℚ, seeded).
The literature is **not yet checked**, so nothing here is claimed new (next test 1). Editing
discipline as for phase notes (≤ 8-line entries). `HARNESS.md` *Evidence* and
*Reproducibility* bind this work; it is not an attack track.

## The question

The formal proofs give the generic body-hinge rank `6(n−1) − def(G̃)` on three strata of `P³`:
panel (KT), molecular (its polar, Phase 25) and pencil (both at once, Phase 40). Which other
subloci of hinge configurations attain it, and when one does not, is its generic rank a clean
count?

## Setting and notation

- A **configuration** of a connected multigraph `G` gives each edge `e = uv` a line, with
  Plücker vector `C_e ≠ 0` in `Λ²K⁴ ≅ K⁶`, over an infinite field `K`. The rank is that of the
  body-hinge rigidity matrix (rows `C_e^⊥ ⊗ (e_u − e_v)`).
- `def_D(G) = max_P D(|P|−1) − (D−1)e(P)` is the blueprint's `def:D-deficiency`. **Here the
  subscript is `D`**, not the main-component chapter's `d`: its `def₂` is `def_3` here, its
  `def₃ = def(G̃)` is `def_6`.
- A **product** stratum lets each hinge range independently over its own family `X_e` of
  lines. A **fibred** stratum is a product once finitely many shared parameters (a common
  point, plane, complex) are fixed. A **coupled** stratum's hinges are determined by per-body
  data (panel, molecular, pencil).

## Results

1. `[PROVED]` **Motion identity.** `rank = 6(n−1) − |E| + rank{g_e ⊗ C_e}`, with `g_e` the
   column of `e` in a cycle-basis matrix (the cographic vectors). A motion modulo the trivial
   ones is a `λ ∈ K^E` with `Σ_{e∈Z} ±λ_e C_e = 0` on every cycle `Z`, and the map from
   motions to `λ` is injective when every `C_e ≠ 0`. Checked at 6 sampled strata
   (`--selftest`). It is the model of `w4/dominance.py`'s `cycle_data`.
2. `[PROVED]` **Product strata: only the linear spans matter.** If each `X_e` is irreducible
   with linear span `L_e`, the generic rank on `∏X_e` equals that on `∏L_e`. Every minor of
   `[g_e ⊗ C_e]` is multilinear in `(C_e)`; a minor vanishing on `∏X_e` is, with the other
   hinges fixed in their `X_f`, linear in `C_e` and zero on `X_e`, so zero on `L_e`; induct
   over the edges. So the Klein quadric costs nothing on a product stratum.
3. `[PROVED]` **The ladder.** If every `L_e` is one space `L` of dimension `D′`, the rank is
   `6(n−1) − def_{D′}(G)`: `{g_e ⊗ C_e}` with `C_e` generic in `L ≅ K^{D′}` represents the
   `D′`-fold union of the cographic matroid, and the union rank formula, taken over flats,
   gives `max_P D′(|P|−1) − (D′−1)e(P)` degrees of freedom. Equivalently, `L^⊥` is a common
   row space worth `(6−D′)(n−1)`, leaving a `D′`-dimensional problem. For differing `L_e` the
   rank is still a matroid-intersection min-max (`[g_e ⊗ C_e]` is spanned by rank-one
   matrices; cf. Lovász 1989, doi:10.1007/BF02585470, details to confirm in next test 1).

   | `D′` | every hinge, independently, … |
   |---|---|
   | 6 | any line (Tay–Whiteley) |
   | 5 | in a fixed linear complex; or meeting a fixed line |
   | 4 | meeting two fixed skew lines |
   | 3 | through a fixed point; in a fixed plane; in one ruling of a fixed quadric (a regulus) |
   | 2 | in a fixed plane through a fixed point of it |

   Check: in a linear complex every cycle of length ≥ 6 loses exactly one degree of freedom
   (`def_5 − def_6`); at `C₆` that is the classical fact that a closed 6R chain whose axes lie
   in a linear complex is infinitesimally mobile.
4. `[PROVED]` **Fibred strata.** With shared parameters `θ`, the generic rank is the maximum
   over `θ` of Result 3's rank for the spans `L_e(θ)` (Result 2 fibre by fibre). This covers,
   e.g., per-body special complexes (the hinges at `v` meet a line `ℓ_v`, so `L_uv` is the
   span of the lines meeting `ℓ_u` and `ℓ_v`), not yet computed (next test 4).
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
   nondegeneracy, not rank.
8. `[PROVED]` incidence fact, rank `OPEN`: **a caution in `P⁴`.** There hinges are planes. On
   the per-body stratum "the hinges at `v` contain a common line `A_v`", adjacent lines `A_u`,
   `A_v` must meet. Three pairwise-meeting lines are concurrent or coplanar, and in the
   coplanar case a triangle's three hinges coincide. Whether the rank drops is unknown, so
   "every per-body stratum attains the generic rank" is not a safe conjecture past `d = 3`.
9. `[INFORMAL]` **The `d = 4` pencil's flat base.** In `P⁴` the pencil (hinges at `v` through
   `p_v` and inside a hyperplane `B_v`) keeps the incidence pattern `p_w ∈ B_v`, `w ∈ N[v]`,
   so the lifting construction has an analogue with pictures in `K³`, though it constrains
   only bodies of degree ≥ 4. With every `B_v = H` the hinges lie in `Λ³H` (`D′ = 4`), and the
   residual is a `D = 4` framework whose hinge vectors at each body lie in a hyperplane: a
   pin-collinear analogue one dimension up (next test 3). Checked less carefully than 1–8.
10. `[CONJECTURED]` **No count formula for arbitrary coupled strata.** Realization spaces of
    incidence configurations can be arbitrarily complicated (Mnëv 1988, LNM 1346,
    doi:10.1007/BFb0082792) and field-dependent (the Fano plane exists only in characteristic
    2). No body-hinge stratum whose rank this changes has been built.

## Evidence

`python3 notes/scripts/strata/strata.py --linear --mixed --perbody --examples --selftest --seed N`,
`N ∈ {1, 2, 3}`, ~20 s each, verdict `OK: every target met` at all three. Per seed: 184
linear cells (23 graphs × 8 rungs) where the rank at a point, the count and the rank at the
per-edge linear envelope agree; 7 mixed cases; every per-body cell (molecular, panel, pencil,
flat pencil) at its count; both `C₆` sentences of Result 6 asserted. Population: the driver's
23 labelled graphs, `n ≤ 12`; a cap, not a census. A point's rank is a lower bound for the
stratum's generic rank and each count an upper bound (Results 3 and 5), so a match certifies
the generic rank on that graph. Sections are drawn once per rung per run; fixed constants
`COORD = 1000`, `SPAN_SAMPLES = 12` (`blindaxes.py --imports`). The self-test rejects a
constructed witness for each of 10 guards, and the subset-DP deficiency agrees with brute-force
partitions and with `kbare_common.exact_deficiency` (131 checks). A GF(p) prototype in the
opening discussion gave the same figures; it is superseded by the driver.

## Next tests (a fresh session)

1. **Literature.** Before treating Results 1–4 as new: Whiteley 1988's matroid-union proof of
   Tay–Whiteley, Jackson–Jordán 2010 (body-bar-and-hinge), Tanigawa 2012 (Dilworth
   truncations), screw-theory sources on 6R chains in a linear complex, and Lovász 1989's
   venue details. The in-tree route to Tay–Whiteley (`thm:body-hinge-tay`) goes through
   bundles of bars and Tay's theorem; Results 1–3 would give a second.
2. **A `d = 4` census of the per-body flag strata** (hinges in `Λ³K⁵`, 9 rows each): common
   flat none / point / line × hyperplane or not, six types, against `10(n−1) − def_10`, on
   the population plus triangle-rich graphs; take Result 8's stratum first. A new mode or a
   sibling driver under `notes/scripts/strata/` (`hybrid_gates.build_rigidity_extensors` is
   `Λ²K⁴`-specific).
3. **Result 9's residual**: the `D = 4` framework with each body's hinge vectors in a
   hyperplane, against `4(n−1) − def_4`.
4. **Result 4's per-body special and linear complexes in `P³`**: does the maximum over the
   parameters reach `def_6`?
5. If the picture survives: Results 1–3 look formalizable as a small phase on the
   matroid-union layer (Phases 12–14) and `def:D-deficiency`. Queuing it is the PI's call.
