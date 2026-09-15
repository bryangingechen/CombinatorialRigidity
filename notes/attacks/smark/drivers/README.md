# `notes/attacks/smark/drivers/` — controls for the smark attack

Exact ℚ (`fractions.Fraction`), stdlib only, every random draw seeded
(`random.Random(20260915)`), every command run with an explicit timeout from
the directory named. These are **controls** for statements in
`notes/pencil/workbook/attack-smark.md`; the deliverable is the proof there.

## `orbits/` — the gauge group `S(ϕ)` on `P⁵` (workbook S1, S4)

Coordinates `x = (x₀; x_u; x_v; x_∞)` = the workbook's `(x_M; x_u; x_v; x_L)`;
group `(a, b, C)` acting by `(ab·x₀; aCx_u; bCx_v; det C·x_∞)`. Run from
`notes/attacks/smark/drivers/orbits/`:

| command | figure it reproduces |
|---|---|
| `timeout 300 python3 task12_orbits.py` | S1(ii): orbit dimension = stratum dimension at 3 exact representatives of each of the 19 strata (`Gen(I)` at `I ∈ {2, −3, 1/2, 1}`); prints `mismatches: none` |
| `timeout 300 python3 task3_semiinvariants.py` | S1(i): the semi-invariant quadratic forms — `span{Q₁, Q₂}` for `χ = ab·det C`, and `x₀²`, `x_∞²` for `a²b²`, `(det C)²`; no others |
| `timeout 300 python3 task45_parity.py` | S4: `dim(star(p) ∩ g·star(p′)) = 1` at 20 pairs × 30 group elements (task 4) and the 16 block defects `≤ 0`; `dim(star(p) ∩ g·Λ²π) = 0` at 20 × 30 (task 5) |
| `timeout 300 python3 task4_genericity_addendum.py` | which of the 20 task-4 pairs deviate from the generic defect vector and why (a zero first/second coordinate of `p` or `p′`) |

Caps, disclosed: representatives and points have numerators in `[−6, 6]` and
denominators in `{1, 2, 3}`; the group sweep is 30 draws per pair, so task 4's
"always 1" is a witness at each draw and task 5's "0 attained" is a witness; the
inequality `dim(A ∩ gB) ≥ 1` for *every* `g` in task 4 is the parity **theorem**
(workbook S4), not the sweep.

## `sideprof.py` — block profile of a side's `ρ̄` at a prescribed generic flag pair (workbook S5)

Run from the repository root. Reuses the corpus samplers and profile code
(`bdecor.sample_by_branches` with `fixed=` flags, `bimage.sample_flags('nonadj')`,
`bimage.rho_bar_of`, `bunif.profile` / `bunif.lam2_mat`, `bdecor.d3` / `weld_d3`);
`tail` (a degree-1 pendant path) goes through a pendant-aware skeleton that calls the
same three `bdecor` primitives, because `bdecor.hubs_and_branches` raises on degree-1
vertices. The 16 block sums are printed in the corpus order with `L` = the line
`p_u p_v` (the workbook's `⟨M⟩`) and `ell` = the line `π_u ∩ π_v` (the workbook's `⟨L⟩`).

| command | figure it reproduces |
|---|---|
| `timeout 900 python3 notes/attacks/smark/drivers/sideprof.py --side all --seed 20260915 --draws 6` | the S5 control table: 11 sides × 6 draws, `ρ = δ` and attaining at 66/66, one profile per side except one `theta34` draw |
| `timeout 600 python3 notes/attacks/smark/drivers/sideprof.py --side theta34 --seed 1 --draws 24` | `theta34`: one profile at 24/24 (the seed-`20260915` deviation is draw-level) |

Caps, disclosed: flag pair and interior points drawn with `s = 20` (numerators in
`[−20, 20]`), 40 tries per branch draw; a "none" excess row is a measurement of the
sampled component at 6 draws, an "excess" row is a lower bound on the generic
`c(U)` (upper semicontinuity of `dim(ρ̄ ∩ U)` on the attaining locus, (BE-37)(i)).
